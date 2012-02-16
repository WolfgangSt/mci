module mci.interpreter.interpreter;

import core.stdc.string,
       core.memory,
       core.thread,
       ffi,
       mci.core.analysis.utilities,
       mci.core.code.modules,
       mci.core.common,
       mci.core.config,
       mci.core.container,
       mci.core.code.functions,
       mci.core.tuple,
       mci.core.typing.core,
       mci.core.typing.members,
       mci.core.typing.types,
       mci.core.code.opcodes,
       mci.interpreter.allocator,
       mci.interpreter.exception,
       mci.core.code.instructions,
       mci.vm.intrinsics.declarations,
       mci.vm.memory.base,
       mci.vm.memory.entrypoint,
       mci.vm.memory.info,
       mci.vm.memory.layout,
       mci.vm.memory.prettyprint,
       mci.vm.thread.thread,
       std.c.stdlib,
       std.stdio,
       std.string,
       std.traits,
       std.utf;

extern (C) void* memcpy(void*, const void*, size_t);
extern (C) void rt_moduleTlsCtor();
extern (C) void rt_moduleTlsDtor();

alias calloc _calloc;
alias free _free;
alias void delegate() ExceptionHandler;

static if (isPosix)
{
    import std.c.linux.linux; 
}

final class InterpreterResult
{
    Type resultType;
    ubyte[] result;
}

private struct InstructionPointer
{
    public Function fun;
    public BasicBlock block;
    public int instructionIndex;
}

private final class ExceptionRecord
{
    public InstructionPointer ip;
    public Type type;
    public ubyte* data;
    private GarbageCollector _gc;
    private InterpreterContext _ctx;

    public this(InterpreterContext ctx, Register exception)
    {
        ip = ctx.ip;
        type = exception.type;
        _gc = ctx._interpreter._gc;
        _ctx = ctx;

        data = cast(ubyte*)_calloc(1, nativeIntSize);
        _gc.addRoot(data);

        *cast(RuntimeObject**)data = *cast(RuntimeObject**)ctx.getValue(exception);
    }

    public void printStackTrace()
    {
        for (auto ctx = _ctx; ctx; ctx = ctx.returnContext)
        {
            auto inst = ctx.ip.block.stream[ctx.ip.instructionIndex - 1];
            writefln("%s.%s.%s: %s", ctx.ip.block.function_.name, ctx.ip.block.name, ctx.ip.instructionIndex - 1, inst.toString());
        }
    }

    public void release()
    {
        _gc.removeRoot(data);
    }
}

private final class InterpreterContext
{
    public InstructionPointer ip;
    public InterpreterContext returnContext;
    public ubyte* returnMem;
    public ubyte*[] args;
    public int _argIndex;
    private Dictionary!(Register, ubyte*, false) _registerState;
    private int _numPushs;
    private Interpreter _interpreter;
    private ExceptionHandler _toplevelHandler;

    // TODO: use utilities:getSignature
    public ReadOnlyIndexable!Type HACK_paramToTypeList(ReadOnlyIndexable!Parameter params)
    {
        NoNullList!Type res = new NoNullList!Type();
        foreach (p; params)
            res.add(p.type);

        return res;
    }

    public void gotoBlock(BasicBlock b)
    {
        ip.block = b;
        ip.instructionIndex = 0;
    }

    public void gotoBlock(string name)
    {
        gotoBlock(ip.fun.blocks[name]);        
    }

    public void gotoEntry()
    {
        gotoBlock("entry");
    }

    public void releaseLocals()
    {
        foreach (r; _registerState)
        {
            auto typ = r.x.type;
            _interpreter._stackAlloc.free(typ);
        }
    }

    public this (Function f, Interpreter interpreter, bool jumpToEntry, ExceptionHandler eh)
    {
        _interpreter = interpreter;
        _toplevelHandler = eh;
        ip.fun = f;

        _registerState = new Dictionary!(Register, ubyte*, false)();
        foreach (namereg; f.registers)
        {
            auto reg = namereg.y;
            auto mem = _interpreter._stackAlloc.allocate(reg.type);
            _registerState.add(reg, mem);
        }

        if (jumpToEntry)
            gotoEntry();
    }

    // dereferences an array or vector element
    public ubyte* arrayElement(Register arrayReg, size_t index, out uint size)
    {
        auto typ = arrayReg.type;
        auto arrayRto = *cast(RuntimeObject**)getValue(arrayReg);
        auto array = arrayRto.data;

        if (auto vec = cast(VectorType)typ)
            size = computeSize(vec.elementType, is32Bit);
        else if (auto arr = cast(ArrayType)typ)
        {
            array += nativeIntSize;
            size = computeSize(arr.elementType, is32Bit);
        }

        return array + index * size;
    }

    // dereferences the first element of an array or vector
    public ubyte* arrayElementFirst(Register arrayReg)
    {
        auto arrayRto = *cast(RuntimeObject**)getValue(arrayReg);
        auto array = arrayRto.data;

        if (auto arr = cast(ArrayType)arrayReg.type)
            array += nativeIntSize;

        return array;
    }

    public ubyte* arrayOrPointerElementFirst(Register reg)
    {
        if (auto arr = cast(PointerType)reg.type)
            return *cast(ubyte**)getValue(reg);
        return arrayElementFirst(reg);
    }

    // dereferences an array or vector or pointer element
    public ubyte* arrayElement(Register arrayReg, Register indexReg, out uint size)
    {
        auto index = *cast(size_t*)getValue(indexReg);
        return arrayElement(arrayReg, index, size);
    }

    // returns the number of elements in an array or vector
    size_t arrayElements(Register arrayReg)
    {
        if (auto arr = cast(VectorType)arrayReg.type)
        {
            return arr.elements;
        }
        else
        {
            auto arrayRto = *cast(RuntimeObject**)getValue(arrayReg);
            return *cast(size_t*)arrayRto.data;
        }
    }

    // (de)references a struct field given a struct pointer or ref
    public ubyte* structElement(Register structReg, Field field, out uint size)
    {
        auto mem = getValue(structReg);
        auto offset = computeOffset(field, is32Bit);
        auto typ = structReg.type;

        size = computeSize(field.type, is32Bit); 

        if (isType!PointerType(typ))
            mem = *cast(ubyte**)mem;
        else if (isType!ReferenceType(typ))
            mem = (*cast(RuntimeObject**)mem).data;

        return mem + offset;
    }

    public void loadRegister(T)(Register reg, InstructionOperand value)
    {
        auto src = value.peek!T();
        auto dst = cast(T*)_registerState[reg];
        *dst = *src;
    }

    public void loadArray(T)(Register reg, InstructionOperand value)
    {
        auto data = *value.peek!(ReadOnlyIndexable!T)();
        allocate(reg, data.count);
        auto dst = arrayOrPointerElementFirst(reg);
        auto mem = cast(T*)dst;
        
        foreach (idx, value; data)
            mem[idx] = value;
    }

    public ubyte* getValue(Register reg)
    {
        return _registerState[reg];
    }

    public void popArg(Register target)
    {
        auto size = computeSize(target.type, is32Bit);
        memcpy(_registerState[target], args[_argIndex++], size);
    }

    struct NullType {};

    private void doConv(T1, T2)(T1* t1, T2* t2)
    {
        //writefln("conv " ~ T2.stringof ~ " [%s] -> " ~ T1.stringof, *t2);
        *t1 = cast(T1)*t2;
    }

    private T opShL(T)(T l, size_t r)
    {
        enum maxBits = T.sizeof * 8;
        if (r >= maxBits)
            return 0;
        return l << r;
    }

    private T opShR(T)(T l, size_t r)
    {
        enum maxBits = T.sizeof * 8;
        static if (isSigned!T)
        {
            if (r >= maxBits)
                return l >> maxBits;
            return l >> r;
        }
        else
        {
            if (r >= maxBits)
                return 0;
            return l >>> r;
        }
    }

    private T opRoR(T)(T l, size_t r)
    {
        enum maxBits = T.sizeof * 8;
        if (r >= maxBits)
            return l;
        return rotate!("right")(l, cast(T)r);
    }

    private T opRoL(T)(T l, size_t r)
    {
        enum maxBits = T.sizeof * 8;
        if (r >= maxBits)
            return l;
        return rotate!("left")(l, cast(T)r);
    }

    private void binaryDispatcher2(string fun, T1=NullType, T2=NullType)(Type t1, Type t2, ubyte* r1, ubyte* r2)
    {
        static if(is(T1 == NullType))
        {
            if (isType!Int8Type(t1))
                return binaryDispatcher2!(fun, T2, byte)(t2, null, r1, r2);

            if (isType!UInt8Type(t1))
                return binaryDispatcher2!(fun, T2, ubyte)(t2, null, r1, r2);

            if (isType!Int16Type(t1))
                return binaryDispatcher2!(fun, T2, short)(t2, null, r1, r2);

            if (isType!UInt16Type(t1))
                return binaryDispatcher2!(fun, T2, ushort)(t2, null, r1, r2);

            if (isType!Int32Type(t1))
                return binaryDispatcher2!(fun, T2, int)(t2, null, r1, r2);

            if (isType!UInt32Type(t1))
                return binaryDispatcher2!(fun, T2, uint)(t2, null, r1, r2);

            if (isType!Int64Type(t1))
                return binaryDispatcher2!(fun, T2, long)(t2, null, r1, r2);

            if (isType!UInt64Type(t1))
                return binaryDispatcher2!(fun, T2, ulong)(t2, null, r1, r2);

            if (isType!Float32Type(t1))
                return binaryDispatcher2!(fun, T2, float)(t2, null, r1, r2);

            if (isType!Float64Type(t1))
                return binaryDispatcher2!(fun, T2, double)(t2, null, r1, r2);

            if (isType!NativeUIntType(t1))
                return binaryDispatcher2!(fun, T2, size_t)(t2, null, r1, r2);

            if (isType!NativeIntType(t1))
                return binaryDispatcher2!(fun, T2, isize_t)(t2, null, r1, r2);

            if (isType!PointerType(t1))
                return binaryDispatcher2!(fun, T2, ubyte*)(t2, null, r1, r2);

            if (isType!ReferenceType(t1))
                return binaryDispatcher2!(fun, T2, RuntimeObject**)(t2, null, r1, r2);

            if (isType!FunctionPointerType(t1))
                return binaryDispatcher2!(fun, T2, ubyte*)(t2, null, r1, r2);

            throw new InterpreterException("Dispatcher cannot deal with " ~ t1.name ~ " yet.");
        } 
        else
        {
            enum string code = fun ~ "!(T2, T1)(cast(T2*)r2, cast(T1*)r1);";
            mixin(code);
        }
    }

    // highlevel D emulation of common ALU instuctions
    private void emulateALUForType(T, string op, bool binary, string resultType, string rhsType)(ubyte* target, ubyte* lhs, ubyte* rhs)
    {
        static if (binary)
        {
            enum string code0 = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")(*cast(T*)lhs " ~ op ~ " *cast(" ~ rhsType ~ "*)rhs);";
            enum string code1 = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")" ~ op ~ "(*cast(T*)lhs, *cast(" ~ rhsType ~ "*)rhs);";
        }
        else
        {
            enum string code0 = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")(" ~ op ~ " *cast(T*)lhs);";
            enum string code1 = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")" ~ op ~ "(*cast(T*)lhs);)";
        }

        static if (__traits(compiles, { mixin(code0); }))
        {
            mixin(code0);
            return;
        } 
        else static if (__traits(compiles, { mixin(code1); }))
        {
            mixin(code1);
            return;
        }
        else
        {
            writeln("Neither of");
            writeln(code0);
            writeln(code1);
            writeln("Is known..");
            throw new InterpreterException("Invalid operation: " ~ op ~ " for " ~ T.stringof);
        }
    }

    private void emulateALU2(string op, bool binary, string resultType="T", string rhsType="T")(Type lhsType, ubyte* dstMem, ubyte* lhsMem, ubyte* rhsMem)
    {
        if (isType!Int8Type(lhsType))
            return emulateALUForType!(byte, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt8Type(lhsType))
            return emulateALUForType!(ubyte, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!Int16Type(lhsType))
            return emulateALUForType!(short, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt16Type(lhsType))
            return emulateALUForType!(ushort, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!Int32Type(lhsType))
            return emulateALUForType!(int, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt32Type(lhsType))
            return emulateALUForType!(uint, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!Int64Type(lhsType))
            return emulateALUForType!(long, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt64Type(lhsType))
            return emulateALUForType!(ulong, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!Float32Type(lhsType))
            return emulateALUForType!(float, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!Float64Type(lhsType))
            return emulateALUForType!(double, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!NativeUIntType(lhsType))
            return emulateALUForType!(size_t, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        if (isType!NativeIntType(lhsType))
            return emulateALUForType!(isize_t, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem);

        throw new InterpreterException("ALU cannot emulate " ~ op ~ " for " ~ lhsType.name ~ " yet.");
    }

    private void emulateALU(string op, bool binary, string resultType="T", string rhsType="T")(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = getValue(inst.sourceRegister1);
        ubyte* rhsMem = null;
        auto dstMem = getValue(inst.targetRegister);

        static if (binary)
            rhsMem = getValue(inst.sourceRegister2);

        emulateALU2!(op, binary, resultType, rhsType)(lhsType, dstMem, lhsMem, rhsMem);
    }

    public bool isArrayOrVector(Type type)
    {
        if (auto arr = cast(ArrayType)type)
                return true;
        if (auto vec = cast(VectorType)type)
                return true;
        return false;
    }

    private void emulateArrayALU(string op, bool binary, string resultType="T", string rhsType="T")(Instruction inst)
    {
        uint dstSize;
        uint lhsSize;
        auto dstMem = arrayElement(inst.sourceRegister1, 0, dstSize);
        auto lhsMem = arrayElement(inst.sourceRegister2, 0, lhsSize);
        uint rhsSize = 0;
        ubyte* rhsMem;
        auto num0 = arrayElements(inst.sourceRegister1);
        auto num1 = arrayElements(inst.sourceRegister2);
        auto typ = getElementType(inst.sourceRegister2.type);
        auto numElements = num0 < num1 ? num0 : num1;

        static if (binary)
        {
            if (isArrayOrVector(inst.sourceRegister3.type))
            {
                auto num2 = arrayElements(inst.sourceRegister3);
                if (num2 < numElements)
                    numElements = num2;
                rhsMem = arrayElement(inst.sourceRegister3, 0, rhsSize);
            }
            else
                rhsMem = getValue(inst.sourceRegister3);
        }

        for (auto i = 0; i < numElements; i++)
        {
            emulateALU2!(op, binary, resultType, rhsType)(typ, dstMem, lhsMem, rhsMem);
            dstMem += dstSize;
            lhsMem += lhsSize;
            rhsMem += rhsSize;
        }
    }

    private ubyte*[] collectArgs()
    {
        if (_numPushs == 0)
            return null;

        auto args = new ubyte*[_numPushs];
        for (auto i = 0; i < _numPushs; i++)
        {
            auto reg = ip.block.stream[ip.instructionIndex - _numPushs - 1 + i].sourceRegister1;
            args[i] = getValue(reg);
        }
        _numPushs = 0;
        return args;
    }

    private void doIntrinsic(Instruction inst)
    {
        auto intrinsic = *inst.operand.peek!Function();

        auto callCtx = returnContext;

        ubyte *dst = null;
        if (intrinsic.returnType)
            dst = callCtx.getValue(inst.targetRegister);

        auto fptr = intrinsicFunctions[intrinsic];

        dispatchFFI(HACK_paramToTypeList(intrinsic.parameters), intrinsic.returnType, CallingConvention.cdecl, fptr, dst, args); 

        releaseLocals();
        switchToContext(callCtx);
    }

    private void dispatchFFI(ReadOnlyIndexable!Type paramTypes, Type _returnType, CallingConvention convention, 
                             FFIFunction entry, ubyte* returnMem, ubyte*[] args)
    {
        try
        {
           _interpreter.dispatchFFI(paramTypes, _returnType, convention, entry, returnMem, args);
        } 
        catch (UnwindException)
        {
            // link the FFIs context.
            // if we do this at FFI call time we might leak all managed stack frames
            // in case the FFI has noreturn semantics
            // The downside of this approach is that stack traces will only work down
            // to the latest FFI that has been unwound
            currentContext.returnContext = this;
            unwindException();
        }
    }

    private void doFFI(Instruction inst)
    {
        auto ffisig = *inst.operand.peek!FFISignature();
        auto fptr = cast(FFIFunction)resolveEntryPoint(ffisig);

        if (fptr is null)
            throw new InterpreterException("Cannot resolve export " ~ ffisig.entryPoint ~ " in " ~ ffisig.library);

        // by specification ffi is the only instruction in the block and
        // the FFI signature corresponds to the current methods signature.
        // The calling convention is specified with the FFI

        auto callCtx = returnContext;

        ubyte* dst = null;
        if (ip.fun.returnType)
        {
            auto callInst = callCtx.ip.block.stream[callCtx.ip.instructionIndex - 1];
            dst = callCtx.getValue(callInst.targetRegister);
        }

        dispatchFFI(HACK_paramToTypeList(ip.fun.parameters), ip.fun.returnType, ip.fun.callingConvention, fptr, dst, args);

        releaseLocals();
        switchToContext(callCtx);
    }

    private void doIndirectFFI(Instruction inst)
    {
        auto ffiSig = cast(FunctionPointerType)inst.sourceRegister1.type;
        auto fptr = *cast(FFIFunction*)getValue(inst.sourceRegister1);

        ubyte* dst = null;
        if (inst.targetRegister)
            dst = getValue(inst.targetRegister);

        dispatchFFI(ffiSig.parameterTypes, ffiSig.returnType, ffiSig.callingConvention, fptr, dst, args);

        throw new InterpreterException("Foreign Function Interfacing not supported yet");
    }

    private void allocate(Register target, size_t count)
    {
        if (auto typ = (cast(ReferenceType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target);
            auto mem = _interpreter.gcallocate(typ, 0);
            *dst = cast(ubyte*)mem;
            return;
        }

        if (auto typ = (cast(PointerType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target);
            if (count == 0)
            {
                *dst = null;
                return;
            }

            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = cast(ubyte*)_calloc(count, elementSize);
            *dst = mem;

            return;
        }

        if (auto typ = (cast(ArrayType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target);
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = _interpreter.gcallocate(typ, count * elementSize);
            *cast(size_t*)mem.data = count;
            *dst = cast(ubyte*)mem;

            return;
        }

        if (auto typ = (cast(VectorType)target.type))
        {
            count = typ.elements;
            auto dst = cast(ubyte**)getValue(target);
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = _interpreter.gcallocate(typ, count * elementSize);       
            *dst = cast(ubyte*)mem;

            return;
        }

        throw new InterpreterException("Unsupported allocate target: " ~ target.name);
    }

    private void convert(Type srcType, Type dstType, ubyte* srcMem, ubyte* dstMem)
    {
        // Type 6 convert
        // T[E] -> U[E] for any valid T -> U conversion.
        if (auto srcVec = cast(VectorType)(srcType))
        {
            auto dstVec = cast(VectorType)(dstType);

            auto srcRto = *cast(RuntimeObject**)srcMem;
            auto dstRto = *cast(RuntimeObject**)dstMem;

            auto dstSize = computeSize(dstVec.elementType, is32Bit);
            auto srcSize = computeSize(srcVec.elementType, is32Bit);

            srcMem = srcRto.data;
            dstMem = dstRto.data;

            for (auto i = 0; i < srcVec.elements; i++)
            {
                binaryDispatcher2!("doConv")(srcVec.elementType, dstVec.elementType, srcMem, dstMem);
                srcMem += srcSize;
                dstMem += dstSize;
            }

            return;
        }

        // Direct conversions

        // Type 1 convert
        // T -> U for any primitives T and U (int8, uint8, int16, uint16, int32, uint32, int64, uint64, int, uint, float32, and float64).

        // Type 2 convert
        // T* -> U* for any T and any U.

        // Type 3 convert
        // T* -> uint or int for any T.

        // Type 4 convert
        // uint or int -> T* for any T.

        // Type 5 convert
        // T& -> U& for any T and any U.

        // Type 7 convert (Direct conversion as pointer type)
        // R1(T1, ...) -> R2(U1, ...) for any R1, any R2, and any amount and type of T n and U m.

        // Type 8 convert (Direct conversion as pointer type)
        // R(T1, ...) -> U* for any R, any amount and type of Tn, and any U.

        // Type 9 convert (Direct conversion as pointer type)
        // T* -> R(U1, ...) for any T, any R, and any amount and type of Un.
        binaryDispatcher2!("doConv")(srcType, dstType, srcMem, dstMem);
    }

    private void unwindException()
    {
        auto lastCtx = this;
        for (auto ctx = this; ctx; ctx = ctx.returnContext)
        {
            auto block = ctx.ip.block.unwindBlock;
            if (block)
            {
                // continue execution here
                ctx.gotoBlock(block);
                switchToContext(ctx);
                return;
            }
            releaseLocals();
            lastCtx = ctx;
        }

        lastCtx._toplevelHandler();
    }

    private void unwindException(Register exceptionRegister)
    {
        auto exception = new ExceptionRecord(this, exceptionRegister);
        setException(exception);
        unwindException();
    }

    @property public bool ready()
    {
        return ip.instructionIndex < ip.block.stream.count;
    }

    public void step()
    {
        auto inst = ip.block.stream[ip.instructionIndex++];

        //writefln("%s.%s.%s: %s", ip.block.function_.name, ip.block.name, ip.instructionIndex - 1, inst.toString());

        // unroll this using metacode if possible for readability
        final switch (inst.opCode.code)
        {
            case OperationCode.nop:
            case OperationCode.comment:
                break;

            case OperationCode.dead:
                writeln("Warning dead code reached");
                break;

            case OperationCode.raw:
                writeln("Interpreter cannot execute raw code");
                break;

            case OperationCode.loadI8:
                loadRegister!byte(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI8:
                loadRegister!ubyte(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI16:
                loadRegister!short(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI16:
                loadRegister!ushort(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI32:
                loadRegister!int(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI32:
                loadRegister!uint(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI64:
                loadRegister!long(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI64:
                loadRegister!ulong(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadF32:
                loadRegister!float(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadF64:
                loadRegister!double(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI8A:
                loadArray!ubyte(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI8A:
                loadArray!byte(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI16A:
                loadArray!ushort(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI16A:
                loadArray!short(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI32A:
                loadArray!uint(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI32A:
                loadArray!int(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadUI64A:
                loadArray!ulong(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadI64A:
                loadArray!long(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadF32A:
                loadArray!float(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadF64A:
                loadArray!double(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadFunc:
                // this assumes that a Function (ref) fits into a function pointer
                loadRegister!Function(inst.targetRegister, inst.operand);
                break;

            case OperationCode.loadNull:
                auto obj = getValue(inst.targetRegister);
                auto sz = computeSize(inst.targetRegister.type, is32Bit);
                memset(obj, 0, sz);
                break;

            case OperationCode.loadSize:
                auto size = computeSize(*inst.operand.peek!Type(), is32Bit);
                *cast(size_t*)getValue(inst.targetRegister) = size;
                break;

            case OperationCode.loadAlign:
                auto alignment = computeAlignment(*inst.operand.peek!Type(), is32Bit);
                *cast(size_t*)getValue(inst.targetRegister) = alignment;
                break;

            case OperationCode.loadOffset:
                auto offset = computeOffset(*inst.operand.peek!Field(), is32Bit);
                *cast(size_t*)getValue(inst.targetRegister) = offset;
                break;

            case OperationCode.fieldGet:
                uint size;
                auto source = structElement(inst.sourceRegister1, *inst.operand.peek!Field(), size);
                auto dest = getValue(inst.targetRegister);
                memcpy(dest, source, size);

                break;

            case OperationCode.fieldSet:
                uint size;
                auto dest = structElement(inst.sourceRegister1, *inst.operand.peek!Field(), size);
                auto source = getValue(inst.sourceRegister2);
                memcpy(dest, source, size);

                break;

            case OperationCode.fieldAddr:
                uint size;
                auto source = structElement(inst.sourceRegister1, *inst.operand.peek!Field(), size);
                auto dest = getValue(inst.targetRegister);

                *cast(ubyte**)dest = source;

                break;

            case OperationCode.fieldStaticGet:
                auto field = *inst.operand.peek!Field();
                auto dest = getValue(inst.targetRegister);
                auto source = _interpreter.getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldStaticSet:
                auto field = *inst.operand.peek!Field();
                auto source = getValue(inst.sourceRegister1);
                auto dest = _interpreter.getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldStaticAddr:
                auto field = *inst.operand.peek!Field();
                auto dest = getValue(inst.targetRegister);
                auto source = _interpreter.getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                *cast(ubyte**)dest = source;
                break;


            case OperationCode.argPush:
                _numPushs++;
                break; // emulation of push is deferred till call instruction

            case OperationCode.argPop:
                popArg(inst.targetRegister);
                break;

            case OperationCode.call:
            case OperationCode.invoke:
                auto target = *inst.operand.peek!Function();

                auto subContext = new InterpreterContext(target, _interpreter, false, null);
                subContext.returnContext = this;
                if (inst.opCode.code == OperationCode.call)
                    subContext.returnMem = getValue(inst.targetRegister);
                subContext.args = collectArgs();

                if (target.attributes == FunctionAttributes.intrinsic)
                    subContext.doIntrinsic(inst);
                else 
                {
                    subContext.gotoEntry();
                    switchToContext(subContext);
                }

                break;

            case OperationCode.callIndirect:
            case OperationCode.invokeIndirect:
                auto funType = cast(FunctionPointerType)inst.sourceRegister1.type;
                auto funPtr = getValue(inst.sourceRegister1);

                if (funType.callingConvention == CallingConvention.standard)
                {
                    auto target = *cast(Function*)funPtr;
                    auto subContext = new InterpreterContext(target, _interpreter, true, null);
                    subContext.returnContext = this;
                    subContext.args = collectArgs();
                    switchToContext(subContext);
                } 
                else
                    doIndirectFFI(inst);
                break;

            case OperationCode.callTail:
            case OperationCode.invokeTail:
                args = collectArgs();
                gotoEntry();
                break;           

            case OperationCode.ariAdd:
                emulateALU!("+", true)(inst);
                break;

            case OperationCode.ariSub:
                emulateALU!("-", true)(inst);
                break;

            case OperationCode.ariMul:
                emulateALU!("*", true)(inst);
                break;

            case OperationCode.ariDiv:
                emulateALU!("/", true)(inst);
                break;

            case OperationCode.ariRem:
                emulateALU!("%", true)(inst);
                break;

            case OperationCode.ariNeg:
                emulateALU!("-", false)(inst);
                break;

            case OperationCode.bitAnd:
                emulateALU!("&", true)(inst);
                break;

            case OperationCode.bitOr:
                emulateALU!("|", true)(inst);
                break;   

            case OperationCode.bitXOr:
                emulateALU!("^", true)(inst);
                break;

            case OperationCode.bitNeg:
                emulateALU!("~", false)(inst);
                break;

            case OperationCode.not:
                emulateALU!("!", false)(inst);
                break;

            case OperationCode.shL:
                emulateALU!("opShL", true, "T", "size_t")(inst);
                break;

            case OperationCode.shR:
                emulateALU!("opShR", true, "T", "size_t")(inst);
                break;

            case OperationCode.roL:
                emulateALU!("opRoL", true, "T", "size_t")(inst);
                break;

            case OperationCode.roR:
                emulateALU!("opRoR", true, "T", "size_t")(inst);
                break;

            case OperationCode.arrayAriAdd:
                emulateArrayALU!("+", true)(inst);
                break;

            case OperationCode.arrayAriSub:
                emulateArrayALU!("-", true)(inst);
                break;

            case OperationCode.arrayAriMul:
                emulateArrayALU!("*", true)(inst);
                break;

            case OperationCode.arrayAriDiv:
                emulateArrayALU!("/", true)(inst);
                break;

            case OperationCode.arrayAriRem:
                emulateArrayALU!("%", true)(inst);
                break;

            case OperationCode.arrayAriNeg:
                emulateArrayALU!("-", false)(inst);
                break;

            case OperationCode.arrayBitAnd:
                emulateArrayALU!("&", true)(inst);
                break;

            case OperationCode.arrayBitOr:
                emulateArrayALU!("|", true)(inst);
                break;

            case OperationCode.arrayBitXOr:
                emulateArrayALU!("^", true)(inst);
                break;

            case OperationCode.arrayBitNeg:
                emulateArrayALU!("~", false)(inst);
                break;

            case OperationCode.arrayNot:
                emulateArrayALU!("!", false)(inst);
                break;

            case OperationCode.arrayShL:
                emulateArrayALU!("opShL", true, "T", "size_t")(inst);
                break;

            case OperationCode.arrayShR:
                emulateArrayALU!("opShR", true, "T", "size_t")(inst);
                break;

            case OperationCode.arrayRoL:
                emulateArrayALU!("opRoL", true, "T", "size_t")(inst);
                break;

            case OperationCode.arrayRoR:
                emulateArrayALU!("opRoR", true, "T", "size_t")(inst);
                break;

            case OperationCode.return_:
                auto src = getValue(inst.sourceRegister1);                
                auto size = computeSize(inst.sourceRegister1.type, is32Bit);
                memcpy(returnMem, src, size);

                releaseLocals();
                switchToContext(returnContext);
                break;

            case OperationCode.leave:
                switchToContext(returnContext);
                releaseLocals();
                break;

            case OperationCode.conv:
                if (inst.targetRegister is inst.sourceRegister1)
                {
                    // debug instruction
                    auto arg = inst.sourceRegister1;
                    writeln( prettyPrint(arg.type, is32Bit, getValue(arg), arg.name ) );
                } 
                else
                {
                    auto srcMem = getValue(inst.sourceRegister1);
                    auto dstMem = getValue(inst.targetRegister);
                    convert(inst.sourceRegister1.type, inst.targetRegister.type, srcMem, dstMem);
                }
                break;

            case OperationCode.arraySet:
                {
                    auto src   = getValue(inst.sourceRegister3);
                    uint size;
                    auto dst = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    memcpy(dst, src, size);
                    break;
                }

            case OperationCode.arrayGet:
                {
                    auto dst = getValue(inst.targetRegister);
                    uint size;
                    auto src = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    memcpy(dst, src, size);
                    break;
                }

            case OperationCode.arrayAddr:
                {
                    auto dst = getValue(inst.targetRegister);
                    uint size;
                    auto src = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    *cast(ubyte**)dst = src;
                    break;
                }

            case OperationCode.arrayLen:
                {
                    auto dst = getValue(inst.targetRegister);
                    if (auto vec = cast(VectorType)inst.sourceRegister1.type)
                    {
                        *cast(size_t*)dst = vec.elements;
                        break;
                    }
                    auto array = (*cast(RuntimeObject**)getValue(inst.sourceRegister1)).data;
                    *cast(size_t*)dst = *cast(size_t*)array;
                    break;
                }

            case OperationCode.jump:
                gotoBlock(*inst.operand.peek!BasicBlock());
                break;

            case OperationCode.jumpCond:
                auto value = *cast(size_t*)getValue(inst.sourceRegister1);
                auto goals = *inst.operand.peek!(Tuple!(BasicBlock, BasicBlock))();
                if (value != 0)
                    gotoBlock(goals.x);
                else 
                    gotoBlock(goals.y);
                break;

            case OperationCode.memAlloc:
                auto count = *cast(size_t*)getValue(inst.sourceRegister1);
                allocate(inst.targetRegister, count);
                break;

            case OperationCode.memNew:
                allocate(inst.targetRegister, 1);
                break;

            case OperationCode.memPin:
                auto rto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                auto handle = _interpreter._gc.pin(rto);
                *cast(size_t*)getValue(inst.targetRegister) = handle;
                break;

            case OperationCode.memUnpin:
                auto handle = *cast(size_t*)getValue(inst.sourceRegister1);
                _interpreter._gc.unpin(handle);
                break;

            case OperationCode.memSet:
                auto size = computeSize(inst.sourceRegister2.type, is32Bit);
                auto dst = *cast(ubyte**)getValue(inst.sourceRegister1);
                auto src = getValue(inst.sourceRegister2);
                memcpy(dst, src, size);

                break;

            case OperationCode.memGet:
                auto size = computeSize(inst.targetRegister.type, is32Bit);
                auto src = *cast(ubyte**)getValue(inst.sourceRegister1);
                auto dst = getValue(inst.targetRegister);
                memcpy(dst, src, size);
                break;

            case OperationCode.memFree:
                auto mem = *cast(ubyte**)getValue(inst.sourceRegister1);
                _free(mem);
                break;

            case OperationCode.memAddr:
                auto mem = getValue(inst.sourceRegister1);
                auto dst = cast(ubyte**)getValue(inst.targetRegister);
                *dst = mem;
                break;

            case OperationCode.cmpEq:
                emulateALU!("==", true, "size_t")(inst);
                break;

            case OperationCode.cmpNEq:
                emulateALU!("!=", true, "size_t")(inst);
                break;

            case OperationCode.cmpGT:
                emulateALU!(">", true, "size_t")(inst);
                break;

            case OperationCode.cmpLT:
                emulateALU!("<", true, "size_t")(inst);
                break;

            case OperationCode.cmpGTEq:
                emulateALU!(">=", true, "size_t")(inst);
                break;

            case OperationCode.cmpLTEq:
                emulateALU!("<=", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpEq:
                emulateArrayALU!("==", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpNEq:
                emulateArrayALU!("!=", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpGT:
                emulateArrayALU!(">", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpLT:
                emulateArrayALU!("<", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpGTEq:
                emulateArrayALU!(">=", true, "size_t")(inst);
                break;

            case OperationCode.arrayCmpLTEq:
                emulateArrayALU!("<=", true, "size_t")(inst);
                break;

            case OperationCode.ffi:
                doFFI(inst);
                break;

            case OperationCode.phi:
                throw new InterpreterException("Phi is invalid in executable ial");

            case OperationCode.ehThrow:
                unwindException(inst.sourceRegister1);
                break;

            case OperationCode.ehRethrow:
                unwindException();
                break;

            case OperationCode.ehCatch:
                *cast(RuntimeObject**)getValue(inst.targetRegister) = *cast(RuntimeObject**)currentException.data;
                break;

            //default:
            //    throw new InterpreterException("Unsupported opcode: " ~ inst.opCode.name);
        }
        //GC.collect();
    }
}

////////////////////////////////////////////////////////////////////////////////
// shared data

private __gshared Dictionary!(Type, FFIType*, false) ffiStructTypeCache;
private __gshared size_t nativeIntSize;
private __gshared UnwindException unwindException;

private class UnwindException : Exception
{
    public this()
    {
        super("Internal unwind exception", __FILE__, __LINE__);
    }
}

shared static this() 
{
    ffiStructTypeCache = new Dictionary!(Type, FFIType*, false);
    nativeIntSize = computeSize(NativeUIntType.instance, is32Bit);
    unwindException = new UnwindException();
}

private FFIType* toFFIType(Type t)
{
    if (t is null)
        return FFIType.ffiVoid; // only valid as return type

    if (isType!UInt8Type(t))
        return FFIType.ffiUByte;

    if (isType!Int8Type(t))
        return FFIType.ffiByte;

    if (isType!UInt16Type(t))
        return FFIType.ffiUShort;

    if (isType!Int16Type(t))
        return FFIType.ffiShort;

    if (isType!UInt32Type(t))
        return FFIType.ffiUInt;

    if (isType!Int32Type(t))
        return FFIType.ffiInt;

    if (isType!UInt64Type(t))
        return FFIType.ffiULong;

    if (isType!Int64Type(t))
        return FFIType.ffiLong;

    // replace with FFI native types rather than is32Bit switch here
    // as soon they are available
    if (isType!NativeIntType(t))
        return is32Bit ? FFIType.ffiInt : FFIType.ffiLong;

    if (isType!NativeUIntType(t))
        return is32Bit ? FFIType.ffiUInt : FFIType.ffiULong;

    if (isType!Float32Type(t))
        return FFIType.ffiFloat;

    if (isType!Float64Type(t))
        return FFIType.ffiDouble;

    if (isType!PointerType(t))
        return FFIType.ffiPointer;

    if (isType!FunctionPointerType(t))
        return FFIType.ffiPointer;

    if (auto struc = cast(StructureType)t)
    {
        synchronized(ffiStructTypeCache)
        {
            if (auto cache = ffiStructTypeCache.get(t))
                return *cache;

            // build a new ffi type
            auto subTypes = new FFIType*[struc.fields.count];
            foreach (idx, field; struc.fields)
                subTypes[idx] = toFFIType(field.y.type);

            auto newItem = new FFIType(subTypes);
            ffiStructTypeCache.add(t, newItem);
            return newItem;
        }
    }

    throw new InterpreterException("Unsupported type for FFI: " ~ t.name);
}

private FFIInterface toFFIConvention(CallingConvention cc)
{
    switch (cc)
    {
        case CallingConvention.cdecl:
            return FFIInterface.platform;
            static if (operatingSystem == OperatingSystem.windows)
            {
                case CallingConvention.stdCall:
                    return FFIInterface.stdCall;
            }
        default:
            throw new InterpreterException("Unsupported calling convention");
    }
}

////////////////////////////////////////////////////////////////////////////////
// per thread data

private InterpreterContext currentContext;
private ExceptionRecord currentException;
private Dictionary!(Tuple!(Interpreter, Field), ubyte*, false) tlsGlobals;

static this()
{    
    tlsGlobals = new Dictionary!(Tuple!(Interpreter, Field), ubyte*, false);
}

static ~this()
{
    // need to release all globals belonging to the threads interpreter here
}

private void step()
{
    currentContext.step();
}

private void run()
{
    while (currentContext && currentContext.ready)
        currentContext.step();
}

private void setException(ExceptionRecord exception)
{
    currentException = exception;
}

private void switchToContext(InterpreterContext context)
{
    currentContext = context;
}

////////////////////////////////////////////////////////////////////////////////
// interpreter helper

public final class Interpreter
{
    private GarbageCollector _gc;
    private Dictionary!(Function, FFIClosure, false) _closureCache;
    private Dictionary!(Field, ubyte*, false) _globals;
    private StackAllocator _stackAlloc;    

    public this(GarbageCollector collector)
    {
        _gc = collector;
        _closureCache = new Dictionary!(Function, FFIClosure, false);
        _globals = new Dictionary!(Field, ubyte*, false);
        _stackAlloc = new StackAllocator(_gc);
    }

    public InterpreterResult interpret(Module mod)
    in
    {
        assert(mod);
    }
    out (result)
    {
        assert(result);
    }
    body
    {
        {
            auto main = mod.functions["main"];
            return runFunction(main);
        }
    }

    ubyte* getGlobal(Field f)
    {
        if (f.storage == FieldStorage.thread)
        {
            auto key = tuple(this, f);
            if (auto cache = tlsGlobals.get(key))
                return *cache;

            return tlsGlobals[key] = cast(ubyte*)_calloc(1, computeSize(f.type, is32Bit));
        } 
        else synchronized(_globals)
        {
            if (auto cache = _globals.get(f))
                return *cache;

            return _globals[f] = cast(ubyte*)_calloc(1, computeSize(f.type, is32Bit));
        }
    }

    private void defaultExceptionHandler()
    {
        auto ex = currentException;
        auto inst = ex.ip.block.stream[ex.ip.instructionIndex - 1];

        writefln("Unhandled exception thrown at %s.%s.%s: %s", ex.ip.block.function_.name, ex.ip.block.name, ex.ip.instructionIndex - 1, inst.toString());
        writeln("==========  Exception  ==========");
        writeln(prettyPrint(ex.type, is32Bit, ex.data, "exception"));
        writeln("========== Stack Trace ==========");
        ex.printStackTrace();
        writeln("=================================");

        throw new InterpreterException("Unhandled ial exception");
    }

    private ubyte*[] serializeArgs(ReadOnlyIndexable!Parameter params, ubyte** argMem)
    {
        auto args = new ubyte*[params.count];

        foreach (idx, p; params)
        {
            auto size = computeSize(p.type, is32Bit);
            auto arg = _stackAlloc.allocate(size);
            memcpy(arg, argMem[idx], size);
            args[idx] = arg;
        }

        return args;
    }

    private void runFunction(Function function_, ubyte* returnMem, ubyte** argMem, ExceptionHandler eh)
    {
        auto context = new InterpreterContext(function_, this, true, eh);

        context.args = serializeArgs(function_.parameters, argMem);
        context.returnMem = returnMem;

        // run
        switchToContext(context);
        run();

        // marshal and free up
        foreach (param; function_.parameters)
            _stackAlloc.free(param.type);
    }

    private void cleanupThread()
    {        
        GC.disable();
        static if (operatingSystem == OperatingSystem.windows)
            thread_detachThis();
        else
            thread_detachByAddr(pthread_self());
        rt_moduleTlsDtor();
        GC.enable();
    }

    private FFIClosure getClosure(Function function_)
    {
        if (auto cache = _closureCache.get(function_))
            return *cache;

        // need a trampoline
        auto params = function_.parameters;
        auto returnType = toFFIType(function_.returnType);
        auto argTypes = new FFIType*[params.count];

        foreach (idx, p; params)
            argTypes[idx] = toFFIType(p.type);

        auto eh = delegate void()
        {
            // we need to abort the current FFI here!
            throw unwindException;           
        };

        // careful, as trampoline invocations from native code consume stack until emulation returns.
        // In case a ffi happens during this emulation with noreturn semantics but rather invoking
        // (semantically a jump instruction within the native code) to another trampoline we will
        // leak this D stackframe.
        // But there is not much we can do about this for the moment.
        auto trampoline = delegate void(void* ret, void** args) 
        { 
            if (!tlsGlobals)
            {
                thread_attachThis();
                rt_moduleTlsCtor();
                registerThreadCleanup(&cleanupThread);
            }
            _gc.attach();
          
            runFunction(function_, cast(ubyte*)ret, cast(ubyte**)args, eh);
        };

        auto cconv = toFFIConvention(function_.callingConvention);
        auto closure = ffiClosure(trampoline, returnType, argTypes, cconv);

        _closureCache.add(function_, closure);
        return closure;
    }

    public RuntimeObject* gcallocate(Type t, size_t additionalSize)
    {
        auto typeInfo = getTypeInfo(t, is32Bit);
        auto r = _gc.allocate(typeInfo, additionalSize);
        return r;
    }

    public void gcfree(RuntimeObject* r)
    {
        _gc.free(r);
    }

    private Function toFunction(ubyte* mem)
    {
        // auto fun = cast(Function)(*cast(ubyte**)mem);
        // Unfortunatley D wont validate the above cast. 
        // We have to do this by ourself here by walking over all currently loaded functions.
        // At the moment we just assume it always is a Function.
        // This wont allow code passing native funcpointers around for the moment.
        //
        // Solution: use the XRefVisitor to collect all funcs during startup and check fun against them

        // This heuristic should work always in practise.
        // All Function objects are GC tracked and thus GC.addrOf() should return non null for any.
        // A pointer to a native entrypoint on the other hand points to code, which address
        // does not belong to any managed code. Thus addrOf returns null.
        // This heuristic is likeley more economic than tracking all Functions as suggested above.

        auto fun = *cast(ubyte**)mem;
        return GC.addrOf(fun) ? cast(Function)fun : null;
    }

    private ubyte* getParamMem(ubyte* mem, Type t)
    {
        if (auto fptr = cast(FunctionPointerType)t)
        {
            // The supplied argument is either a native function pointer or a pointer to a Function object. 
            // In the latter case we need to create a trampoline to the emulator

            if (auto fun = toFunction(mem))
                return cast(ubyte*)getClosure(fun).function_;
            
            return mem;
        }
        return mem;
    }

    public void dispatchFFI(ReadOnlyIndexable!Type paramTypes, Type _returnType, CallingConvention convention, 
                            FFIFunction entry, ubyte* returnMem, ubyte*[] args)
    {
        auto returnType = toFFIType(_returnType);
        auto argTypes = new FFIType*[paramTypes.count];
        auto argMem = new void*[paramTypes.count];
        auto cconv = toFFIConvention(convention);

        foreach (idx, p; paramTypes)
        {
            argTypes[idx] = toFFIType(p);
            argMem[idx] = getParamMem(args[idx], p);
        }

        ffiCall(entry, returnType, argTypes, returnMem, argMem, cconv); 
    }

    // TODO: cleanup double allocs once stuff works again
    InterpreterResult runFunction(Function fun)
    {
        auto context = new InterpreterContext(fun, this, true, &defaultExceptionHandler);
        auto returnType = fun.returnType;
        if (returnType)
            context.returnMem = cast(ubyte*)_calloc(1, computeSize(returnType, is32Bit));
        switchToContext(context);
        run();

        auto result = new InterpreterResult();
        result.resultType = returnType;
        if (returnType)
        {
            auto resultSize = computeSize(returnType, is32Bit);
            result.result = new ubyte[resultSize];
            memcpy(result.result.ptr, context.returnMem, resultSize);
            _free(context.returnMem);

            writeln("The program quitted with:");
            writeln( prettyPrint( result.resultType, is32Bit, result.result.ptr, "(return value)" ) );
        } 
        else
            writeln("The program quitted without return value.");
        
        return result;
    }
}
