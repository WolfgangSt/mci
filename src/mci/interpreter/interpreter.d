module mci.interpreter.interpreter;

import core.atomic,
       core.stdc.string,
       core.memory,
       core.thread,
       ffi,
       mci.core.analysis.utilities,
       mci.core.code.modules,
       mci.core.common,
       mci.core.config,
       mci.core.container,
       mci.core.code.functions,
       mci.core.math,
       mci.core.memory,
       mci.core.sync,
       mci.core.tuple,
       mci.core.typing.core,
       mci.core.typing.members,
       mci.core.typing.types,
       mci.core.weak,
       mci.core.code.opcodes,
       mci.interpreter.allocator,
       mci.interpreter.debuggee,
       mci.interpreter.exception,
       mci.core.code.instructions,
       mci.vm.exception,
       mci.vm.execution,
       mci.vm.intrinsics.context,
       mci.vm.intrinsics.declarations,
       mci.vm.memory.base,
       mci.vm.ffi,
       mci.vm.memory.info,
       mci.vm.memory.layout,
       mci.vm.memory.prettyprint,
       mci.vm.threading.cleanup,
       mci.vm.trace,
       std.c.stdlib,
       std.socket,
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
alias mci.core.config.is32Bit is32Bit;
alias core.atomic.atomicLoad atomicLoad;

enum bool longjmpUnwind = true;

static if (isPOSIX)
{
    import std.c.linux.linux;
}

static if (architecture == Architecture.x86)
{
    import core.cpuid;
}

static if (longjmpUnwind)
{
    static if (isPOSIX)
    {
        import core.sys.posix.setjmp;
    }
    else
    {
        static assert(false, "longjmp is only supported for POSIX systems.");
    }
}

private struct InstructionPointer
{
    public Function fun;
    public BasicBlock block;
    public uint instructionIndex;
}

private final class ExceptionRecord
{
    public InstructionPointer ip;
    public Type type;
    public RuntimeObject** data;
    private GarbageCollector _gc;
    private InterpreterContext _ctx;

    public this(InterpreterContext ctx, Register exception)
    {
        ip = ctx.ip;
        type = exception.type;
        _gc = ctx._interpreter._gc;
        _ctx = ctx;

        data = cast(RuntimeObject**)_calloc(1, nativeIntSize);
        _gc.addRoot(data);

        *data = *cast(RuntimeObject**)ctx.getValue(exception);
    }

    public NoNullList!StackFrame getFrames()
    {
        auto frames = new NoNullList!StackFrame();
        for (auto ctx = _ctx; ctx; ctx = ctx.returnContext)
        {
            auto inst = ctx.ip.block.stream[ctx.ip.instructionIndex - 1];
            frames.add(new StackFrame(inst));
        }
        return frames;
    }

    public RuntimeValue toRuntimeValue()
    {
        auto rv = new RuntimeValue(_gc, type);
        *cast(RuntimeObject**)rv.data = *data;
        return rv;
    }

    public void release()
    {
        _gc.removeRoot(data);
        *data = null;
    }
}

private final class InterpreterContext
{
    public InstructionPointer ip;
    public InterpreterContext returnContext;
    public bool nativeTransition; // stop flag that signals run() to return once this stackframe is reached
    public ubyte* returnMem;
    public ubyte*[] args;
    private int _argIndex;
    private Dictionary!(Register, ubyte*, false) _registerState;
    private Dictionary!(Register, ubyte*, false) _shadowState;
    private int _numPushs;
    private Interpreter _interpreter;
    private ExceptionHandler _toplevelHandler;

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
        if (_shadowState !is null)
        {
            foreach (r; _shadowState)
            {
                auto typ = r.x.type;
                _interpreter._stackAlloc.free(typ);
            }
        }

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

        allocateLocals();

        if (jumpToEntry)
            gotoEntry();
    }

    private void allocateLocals()
    {
        _registerState = new typeof(_registerState)();
        foreach (namereg; ip.fun.registers)
        {
            auto reg = namereg.y;
            auto mem = _interpreter._stackAlloc.allocate(reg.type);
            _registerState.add(reg, mem);
        }
    }

    // required for tail calls
    private void shadowLocals()
    {
        auto oldShadow = _shadowState;
        _shadowState = _registerState;

        if (oldShadow is null)
            allocateLocals();
        else
        {
            _registerState = oldShadow;
            foreach (r; _registerState)
                memset(r.y, 0, computeSize(r.x.type, is32Bit));
        }
    }

    // dereferences an array or vector element
    public ubyte* arrayElement(Register arrayReg, size_t index, out size_t size)
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

        return alignArray(array) + index * size;
    }

    // dereferences the first element of an array or vector
    public ubyte* arrayElementFirst(Register arrayReg)
    {
        auto arrayRto = *cast(RuntimeObject**)getValue(arrayReg);
        auto array = arrayRto.data;

        if (auto arr = cast(ArrayType)arrayReg.type)
            array += nativeIntSize;

        return alignArray(array);
    }

    public ubyte* arrayOrPointerElementFirst(Register reg)
    {
        if (auto arr = cast(PointerType)reg.type)
            return *cast(ubyte**)getValue(reg);
        return arrayElementFirst(reg);
    }

    // dereferences an array or vector or pointer element
    public ubyte* arrayElement(Register arrayReg, Register indexReg, out size_t size)
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
    public ubyte* structElement(Register structReg, Field field, out size_t size)
    {
        auto mem = getValue(structReg);
        auto offset = computeOffset(field, is32Bit);
        auto typ = structReg.type;

        size = computeSize(field.type, is32Bit);

        if (cast(PointerType)typ)
            mem = *cast(ubyte**)mem;
        else if (cast(ReferenceType)typ)
            mem = (*cast(RuntimeObject**)mem).data;

        return mem + offset;
    }

    public void loadRegister(T)(Register reg, InstructionOperand value)
    {
        auto src = value.peek!T();
        static if (is(T == Function))
        {
            if ((cast(FunctionPointerType)reg.type).callingConvention == CallingConvention.standard)
            {
                auto dst = cast(T*)_registerState[reg];
                *dst = *src;
            }
            else
            {
                auto dst = cast(FFIFunction*)_registerState[reg];
                *dst = *_interpreter.getClosure!(Function, false)(*src).function_;
            }
        }
        else
        {
            auto dst = cast(T*)_registerState[reg];
            *dst = *src;
        }
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

    private void binaryDispatcher2(string fun, T1 = NullType, T2 = NullType)(Type t1, Type t2, ubyte* r1, ubyte* r2)
    {
        static if (is(T1 == NullType))
        {
            match(t1,
                  (Int8Type t) => binaryDispatcher2!(fun, T2, byte)(t2, null, r1, r2),
                  (UInt8Type t) => binaryDispatcher2!(fun, T2, ubyte)(t2, null, r1, r2),
                  (Int16Type t) => binaryDispatcher2!(fun, T2, short)(t2, null, r1, r2),
                  (UInt16Type t) => binaryDispatcher2!(fun, T2, ushort)(t2, null, r1, r2),
                  (Int32Type t) => binaryDispatcher2!(fun, T2, int)(t2, null, r1, r2),
                  (UInt32Type t) => binaryDispatcher2!(fun, T2, uint)(t2, null, r1, r2),
                  (Int64Type t) => binaryDispatcher2!(fun, T2, long)(t2, null, r1, r2),
                  (UInt64Type t) => binaryDispatcher2!(fun, T2, ulong)(t2, null, r1, r2),
                  (Float32Type t) => binaryDispatcher2!(fun, T2, float)(t2, null, r1, r2),
                  (Float64Type t) => binaryDispatcher2!(fun, T2, double)(t2, null, r1, r2),
                  (NativeUIntType t) => binaryDispatcher2!(fun, T2, size_t)(t2, null, r1, r2),
                  (NativeIntType t) => binaryDispatcher2!(fun, T2, isize_t)(t2, null, r1, r2),
                  (PointerType t) => binaryDispatcher2!(fun, T2, ubyte*)(t2, null, r1, r2),
                  (ReferenceType t) => binaryDispatcher2!(fun, T2, RuntimeObject**)(t2, null, r1, r2),
                  (FunctionPointerType t) => binaryDispatcher2!(fun, T2, ubyte*)(t2, null, r1, r2),
                  ()
                  {
                      throw new InterpreterException("Dispatcher cannot deal with " ~ t1.name ~ " yet.");
                  });
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

    private void emulateALU2(string op, bool binary, string resultType = "T", string rhsType = "T")(Type lhsType, ubyte* dstMem, ubyte* lhsMem, ubyte* rhsMem)
    {
        match(lhsType,
              (Int8Type t) => emulateALUForType!(byte, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (UInt8Type t) => emulateALUForType!(ubyte, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (Int16Type t) => emulateALUForType!(short, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (UInt16Type t) => emulateALUForType!(ushort, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (Int32Type t) => emulateALUForType!(int, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (UInt32Type t) => emulateALUForType!(uint, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (Int64Type t) => emulateALUForType!(long, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (UInt64Type t) => emulateALUForType!(ulong, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (Float32Type t) => emulateALUForType!(float, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (Float64Type t) => emulateALUForType!(double, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (NativeUIntType t) => emulateALUForType!(size_t, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              (NativeIntType t) => emulateALUForType!(isize_t, op, binary, resultType, rhsType)(dstMem, lhsMem, rhsMem),
              ()
              {
                  throw new InterpreterException("ALU cannot emulate " ~ op ~ " for " ~ lhsType.name ~ " yet.");
              });
    }

    private void emulateALU(string op, bool binary, string resultType = "T", string rhsType = "T")(Instruction inst)
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

    private void emulateArrayALU(string op, bool binary, string resultType = "T", string rhsType = "T")(Instruction inst)
    {
        size_t dstSize;
        size_t lhsSize;
        auto dstMem = arrayElement(inst.sourceRegister1, 0, dstSize);
        auto lhsMem = arrayElement(inst.sourceRegister2, 0, lhsSize);
        size_t rhsSize = 0;
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

        dispatchFFI!true(intrinsic.parameters, intrinsic.returnType, CallingConvention.cdecl, fptr, dst, args);

        releaseLocals();
        switchToContext(callCtx);
    }

    private void doIndirectIntrinsic(Instruction inst)
    {
        auto ffiSig = cast(FunctionPointerType)inst.sourceRegister1.type;
        auto intrinsic = *cast(Function*)getValue(inst.sourceRegister1);
        auto fptr = intrinsicFunctions[intrinsic];

        ubyte* dst = null;
        if (inst.targetRegister)
            dst = getValue(inst.targetRegister);

        dispatchFFI!true(ffiSig.parameterTypes, ffiSig.returnType, ffiSig.callingConvention, fptr, dst, args);
    }

    private void dispatchFFI(bool isIntrinsic, T)(ReadOnlyIndexable!T paramTypes, Type _returnType, CallingConvention convention,
                             FFIFunction entry, ubyte* returnMem, ubyte*[] args)
    {
        try
        {
            _interpreter.dispatchFFI!isIntrinsic(paramTypes, _returnType, convention, entry, returnMem, args);
        }
        catch (UnwindException)
        {
            // link the FFIs context.
            // if we do this at FFI call time we might leak all managed stack frames
            // in case the FFI has noreturn semantics
            // The downside of this approach is that stack traces will only work down
            // to the latest FFI that has been unwound
            //currentContext.returnContext = this;
            unwindException();
        }
    }

    private void doFFI(Instruction inst)
    {
        auto ffisig = *inst.operand.peek!FFISignature();
        auto fptr = cast(FFIFunction)_interpreter.resolveEntryPoint(ffisig);

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

        dispatchFFI!false(ip.fun.parameters, ip.fun.returnType, ip.fun.callingConvention, fptr, dst, args);

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

        dispatchFFI!false(ffiSig.parameterTypes, ffiSig.returnType, ffiSig.callingConvention, fptr, dst, args);
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
            auto mem = _interpreter.gcallocate(typ, count * elementSize + maxPadding);
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
            auto mem = _interpreter.gcallocate(typ, maxPadding);
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
            if (ctx.nativeTransition)
                break;
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

        // check for debugging
        //if (_interpreter.)

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

            case OperationCode.tramp:
                auto srcType = cast(FunctionPointerType)inst.sourceRegister1.type;
                switch (srcType.callingConvention)
                {
                    case CallingConvention.standard:
                        auto src = cast(Function*)getValue(inst.sourceRegister1);
                        auto dst = cast(FFIFunction*)getValue(inst.targetRegister);
                        *dst = *_interpreter.getClosure(*src).function_;
                        break;
                    default:
                        auto dstType = cast(FunctionPointerType)inst.targetRegister.type;
                        auto src = cast(FFIFunction*)getValue(inst.sourceRegister1);
                        auto dst = cast(FFIFunction*)getValue(inst.targetRegister);
                        *dst = *_interpreter.getClosure(srcType, dstType, *src).function_;
                }
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
                auto field = *inst.operand.peek!Field();
                auto fieldType = field.type;
                auto source = getValue(inst.sourceRegister1);
                auto dest = getValue(inst.targetRegister);
                auto offset = computeOffset(field, is32Bit);
                auto memType = inst.sourceRegister1.type;
                auto mem = getValue(inst.sourceRegister1);

                if (cast(ReferenceType)memType)
                {
                    auto rto = *cast(RuntimeObject**)mem;
                    mem = rto.data;

                    if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                    {
                        if (barrier.barriers & BarrierFlags.fieldGet && isManaged(fieldType))
                        {
                            auto ptr = cast(RuntimeObject**)(mem + offset);
                            barrier.fieldGetBarrier(rto, field, ptr, cast(RuntimeObject**)dest);
                            break;
                        }
                    }
                }
                else if (cast(PointerType)memType)
                    mem = *cast(ubyte**)mem;

                mem += offset;
                auto size = computeSize(fieldType, is32Bit);
                memcpy(dest, mem, size);
                break;

            case OperationCode.fieldSet:
                auto field = *inst.operand.peek!Field();
                auto fieldType = field.type;
                auto source = getValue(inst.sourceRegister2);
                auto dest = getValue(inst.sourceRegister1);
                auto offset = computeOffset(field, is32Bit);
                auto memType = inst.sourceRegister1.type;
                auto mem = getValue(inst.sourceRegister1);

                if (cast(ReferenceType)memType)
                {
                    auto rto = *cast(RuntimeObject**)mem;
                    mem = rto.data;

                    if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                    {
                        if (barrier.barriers & BarrierFlags.fieldSet && isManaged(fieldType))
                        {
                            auto ptr = cast(RuntimeObject**)(mem + offset);
                            barrier.fieldSetBarrier(rto, field, ptr, cast(RuntimeObject**)source);
                            break;
                        }
                    }
                }
                else if (cast(PointerType)memType)
                    mem = *cast(ubyte**)mem;

                mem += offset;
                auto size = computeSize(fieldType, is32Bit);
                memcpy(mem, source, size);
                break;

            case OperationCode.fieldAddr:
                size_t size;
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

            case OperationCode.fieldUserGet:
                auto rto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                auto dest = getValue(inst.targetRegister);

                if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                {
                    if (barrier.barriers & BarrierFlags.fieldGet)
                    {
                        auto ptr = &rto.userData;
                        barrier.fieldGetBarrier(rto, null, ptr, cast(RuntimeObject**)dest);
                        break;
                    }
                }

                *cast(RuntimeObject**)dest = rto.userData;
                break;

            case OperationCode.fieldUserSet:
                auto rto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                auto source = getValue(inst.sourceRegister2);

                if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                {
                    if (barrier.barriers & BarrierFlags.fieldSet)
                    {
                        auto ptr = &rto.userData;
                        barrier.fieldSetBarrier(rto, null, ptr, cast(RuntimeObject**)source);
                        break;
                    }
                }

                rto.userData = *cast(RuntimeObject**)source;
                break;

            case OperationCode.fieldUserAddr:
                auto rto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                auto dest = getValue(inst.targetRegister);
                *cast(RuntimeObject***)dest = &rto.userData;
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
                else if (auto target = toFunction(funPtr))
                    doIndirectIntrinsic(inst);
                else
                    doIndirectFFI(inst);
                break;

            case OperationCode.callTail:
            case OperationCode.invokeTail:
                args = collectArgs();
                shadowLocals();
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
                    auto source = getValue(inst.sourceRegister3);
                    auto elementType = inst.sourceRegister3.type;
                    auto arrayRto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                    auto index = *cast(size_t*)getValue(inst.sourceRegister2);
                    auto array = arrayRto.data;
                    auto elementSize = computeSize(elementType, is32Bit);

                    if (auto arr = cast(ArrayType)inst.sourceRegister1.type)
                        array += nativeIntSize;

                    array = alignArray(array) + elementSize * index;

                    if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                    {
                        if (barrier.barriers & BarrierFlags.arraySet && isManaged(elementType))
                        {
                            barrier.arraySetBarrier(arrayRto, index, cast(RuntimeObject**)(array), cast(RuntimeObject**)source);
                            break;
                        }
                    }

                    memcpy(array, source, elementSize);
                    break;
                }

            case OperationCode.arrayGet:
                {
                    auto dest = getValue(inst.targetRegister);
                    auto elementType = inst.targetRegister.type;
                    auto arrayRto = *cast(RuntimeObject**)getValue(inst.sourceRegister1);
                    auto index = *cast(size_t*)getValue(inst.sourceRegister2);
                    auto array = arrayRto.data;
                    auto elementSize = computeSize(elementType, is32Bit);

                    if (auto arr = cast(ArrayType)inst.sourceRegister1.type)
                        array += nativeIntSize;

                    array = alignArray(array) + elementSize * index;

                    if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                    {
                        if (barrier.barriers & BarrierFlags.arrayGet && isManaged(elementType))
                        {
                            barrier.arrayGetBarrier(arrayRto, index, cast(RuntimeObject**)(array), cast(RuntimeObject**)dest);
                            break;
                        }
                    }

                    memcpy(dest, array, elementSize);
                    break;
                }

            case OperationCode.arrayAddr:
                {
                    auto dst = getValue(inst.targetRegister);
                    size_t size;
                    auto src = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    *cast(ubyte**)dst = src;
                    break;
                }

            case OperationCode.arrayLen:
                {
                    auto dst = getValue(inst.targetRegister);
                    *cast(size_t*)dst = arrayElements(inst.sourceRegister1);
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
            case OperationCode.memSAlloc:
                auto count = *cast(size_t*)getValue(inst.sourceRegister1);
                allocate(inst.targetRegister, count);
                break;

            case OperationCode.memNew:
            case OperationCode.memSNew:
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
                auto dst = getValue(inst.sourceRegister1);
                auto src = getValue(inst.sourceRegister2);

                if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                {
                    if (barrier.barriers & BarrierFlags.memorySet && isManaged(inst.sourceRegister2.type))
                    {
                        barrier.memorySetBarrier(cast(RuntimeObject**)dst, cast(RuntimeObject**)src);
                        break;
                    }
                }

                memcpy(*cast(ubyte**)dst, src, size);
                break;

            case OperationCode.memGet:
                auto size = computeSize(inst.targetRegister.type, is32Bit);
                auto src = getValue(inst.sourceRegister1);
                auto dst = getValue(inst.targetRegister);

                if (auto barrier = cast(AtomicGarbageCollector)_interpreter.gc)
                {
                    if (barrier.barriers & BarrierFlags.memoryGet && isManaged(inst.targetRegister.type))
                    {
                        barrier.memoryGetBarrier(cast(RuntimeObject**)src, cast(RuntimeObject**)dst);
                        break;
                    }
                }

                memcpy(dst, *cast(ubyte**)src, size);
                break;

            case OperationCode.memFree:
                auto mem = *cast(ubyte**)getValue(inst.sourceRegister1);
                if (cast(PointerType)inst.sourceRegister1.type)
                    _free(mem);
                else
                    _interpreter._gc.free(cast(RuntimeObject*)mem);
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
                *cast(RuntimeObject**)getValue(inst.targetRegister) = *currentException.data;
                currentException.release();
                setException(null);
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
private __gshared Mutex ffiStructTypeCacheMutex;
private __gshared size_t nativeIntSize;
private __gshared UnwindException unwindException;
private __gshared size_t maxPadding;
private __gshared size_t sseAlignment;

private class UnwindException : Exception
{
    public this()
    {
        super("Internal unwind exception", __FILE__, __LINE__);
    }
}

shared static this()
{
    ffiStructTypeCache = new typeof(ffiStructTypeCache)();
    ffiStructTypeCacheMutex = new Mutex();
    nativeIntSize = computeSize(NativeUIntType.instance, is32Bit);
    unwindException = new UnwindException();

    static if (architecture == Architecture.x86)
    {
        sseAlignment = size_t.sizeof;
        if (sse)
            sseAlignment = 16;
        if (avx)
            sseAlignment = 32;
    }
    else
        sseAlignment = 32;

    maxPadding = sseAlignment - size_t.sizeof;
}

ubyte* alignArray(ubyte* mem)
{
    auto al = alignTo(cast(size_t)mem, sseAlignment);
    assert((al % sseAlignment) == 0);
    return cast(ubyte*)al;
}

private FFIType* toFFIType(Type type)
{
    return match(type,
                 (UInt8Type t) => FFIType.ffiUByte,
                 (Int8Type t) => FFIType.ffiByte,
                 (UInt16Type t) => FFIType.ffiUShort,
                 (Int16Type t) => FFIType.ffiShort,
                 (UInt32Type t) => FFIType.ffiUInt,
                 (Int32Type t) => FFIType.ffiInt,
                 (UInt64Type t) => FFIType.ffiULong,
                 (Int64Type t) => FFIType.ffiLong,
                 (NativeIntType t) => is32Bit ? FFIType.ffiInt : FFIType.ffiLong,
                 (NativeUIntType t) => is32Bit ? FFIType.ffiUInt : FFIType.ffiULong,
                 (Float32Type t) => FFIType.ffiFloat,
                 (Float64Type t) => FFIType.ffiDouble,
                 (PointerType t) => FFIType.ffiPointer,
                 (FunctionPointerType t) => FFIType.ffiPointer,
                 (StructureType t)
                 {
                     ffiStructTypeCacheMutex.lock();

                     scope (exit)
                         ffiStructTypeCacheMutex.unlock();

                     if (auto cache = ffiStructTypeCache.get(t))
                         return *cache;

                     // build a new ffi type
                     auto subTypes = new FFIType*[t.fields.count];
                     foreach (idx, field; t.fields)
                         subTypes[idx] = toFFIType(field.y.type);

                     auto newItem = new FFIType(subTypes);
                     ffiStructTypeCache.add(t, newItem);
                     return newItem;
                 },
                 ()
                 {
                     if (type is null)
                         return FFIType.ffiVoid; // only valid as return type
                     throw new InterpreterException("Unsupported type for FFI: " ~ type.name);
                 });
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

////////////////////////////////////////////////////////////////////////////////
// per thread data

private InterpreterContext currentContext;
private ExceptionRecord currentException;
private Dictionary!(Tuple!(Weak!Interpreter, Field), ubyte*, false) tlsGlobals;
private size_t localTLSColor;
private __gshared size_t globalTLSColor;

static this()
{
    tlsGlobals = new typeof(tlsGlobals)();
}

private void compactTLSGlobals()
{
    while (true)
    {
        auto globalColor = atomicLoad(*cast(shared)&globalTLSColor);
        if (localTLSColor == globalColor)
            break;

        localTLSColor = globalColor;
        auto compactedGlobals = new Dictionary!(Tuple!(Weak!Interpreter, Field), ubyte*, false);
        foreach (kv; tlsGlobals)
        {
            if (kv.x.x.getObject())
                compactedGlobals.add(kv.x, kv.y);
        }
        tlsGlobals = compactedGlobals;
    }
}

private void step()
{
    currentContext.step();
}

private void run()
{
    while (currentContext)
    {
        if (currentContext.nativeTransition)
        {
            currentContext.nativeTransition = false;
            return;
        }
        currentContext.step();
    }
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

public final class Interpreter : ExecutionEngine
{
    private Weak!Interpreter _weakThis;
    private GarbageCollector _gc;
    private Dictionary!(Function, FFIClosure, false) _closureCache;
    private Dictionary!(Field, ubyte*, false) _globals;
    private Mutex _globalsMutex;
    private StackAllocator _stackAlloc;
    private VirtualMachineContext _vmContext;
    private InterpreterDebuggerServer _debugger;
    private Dictionary!(string, void*) _ffiLibraries;
    private Dictionary!(Tuple!(string, string), EntryPoint) _ffiEntrypoints;
    private HashSet!Module _loadedModules;
    private HashSet!Thread _attachedThreads;
    private Mutex _loadedModulesMutex;
    private Mutex _attachedThreadsMutex;

    public this(GarbageCollector gc)
    in
    {
        assert(gc);
    }
    body
    {
        super(gc);
        _weakThis = new Weak!Interpreter(this);
        _gc = gc;
        _closureCache = new typeof(_closureCache)();
        _globals = new typeof(_globals)();
        _globalsMutex = new Mutex();
        _stackAlloc = new StackAllocator(_gc);
        //_debugger = new InterpreterDebuggerServer(this);
        _vmContext = context;
        _ffiLibraries = new typeof(_ffiLibraries)();
        _ffiEntrypoints = new typeof(_ffiEntrypoints)();
        _loadedModules = new typeof(_loadedModules)();
        _attachedThreads = new typeof(_attachedThreads)();
        _loadedModulesMutex = new Mutex();
        _attachedThreadsMutex = new Mutex();
    }

    public override void terminate()
    {
        super.terminate(); // do this after thread exits?

        detachFromMCIRuntime();

        {
            _attachedThreadsMutex.lock();

            scope (exit)
                _attachedThreadsMutex.unlock();

            foreach (thread; _attachedThreads)
                writefln("Warning: Thread %s did not detach from runtime, it wont invoke any thread exit point anymore!", cast(void*)thread);
        }


        // Notice other threads that an Interpreter died. During their next TLS access
        // they will sync their thread local tlsGlobals using compactTLSGlobals()
        atomicOp!"+="(*cast(shared)&globalTLSColor, 1);

        // unload all ffi librarys
        foreach (void* lib; _ffiLibraries.values)
            closeLibrary(lib);

        _stackAlloc.cleanup();
        _gc.collect();

        if (auto igc = cast(InteractiveGarbageCollector)_gc)
            igc.waitForFreeCallbacks();
    }

    public override RuntimeValue execute(Function function_, NoNullList!RuntimeValue arguments)
    in
    {
        assert(function_);
        assert(arguments);
        assert(arguments.count == function_.parameters.count);

        foreach (i, arg; arguments)
            assert(arg is function_.parameters[i].type);
    }
    out (result)
    {
        assert(function_.returnType ? !!result : !result);
    }
    body
    {
        {
            _loadedModulesMutex.lock();

            scope (exit)
                _loadedModulesMutex.unlock();

            _loadedModules.add(function_.module_);
        }
        attachToRuntime();

        auto context = new InterpreterContext(function_, this, true, &defaultExceptionHandler);
        auto returnType = function_.returnType;
        RuntimeValue result;

        if (returnType)
        {
            result = new RuntimeValue(_gc, returnType);
            context.returnMem = result.data;
        }

        auto numArgs = arguments.count;
        if (numArgs > 0)
        {
            auto args = new ubyte*[numArgs];
            foreach (i, arg; arguments)
                args[i] = arg.data;
            context.args = args;
        }

        context.returnContext = currentContext;
        if (context.returnContext)
            context.returnContext.nativeTransition = true;

        switchToContext(context);
        if (_debugger)
            _debugger.waitForDebugger(context.ip);
        run();

        return result;
    }

    public override RuntimeValue execute(function_t function_, CallingConvention callingConvention, Type returnType, NoNullList!RuntimeValue arguments)
    {
        if (callingConvention == CallingConvention.standard)
        {
            // function will be a Function reference as it was loaded via a load.func of this interpreter
            // at an earlier point
            return execute(cast(Function)function_, arguments);
        }

        // invoke via FFI
        RuntimeValue result;
        ubyte* returnMem;
        if (returnType)
        {
            result = new RuntimeValue(_gc, returnType);
            returnMem = result.data;
        }

        attachToRuntime();
        dispatchFFI!false(arguments, returnType, callingConvention, function_, returnMem, arguments);
        return result;
    }

    private ubyte* getGlobal(Field f)
    {
        if (f.storage == FieldStorage.thread)
        {
            compactTLSGlobals();
            auto key = tuple(_weakThis, f);
            if (auto cache = tlsGlobals.get(key))
                return *cache;

            return tlsGlobals[key] = cast(ubyte*)_calloc(1, computeSize(f.type, is32Bit));
        }
        else
        {
            _globalsMutex.lock();

            scope (exit)
                _globalsMutex.unlock();

            if (auto cache = _globals.get(f))
                return *cache;

            return _globals[f] = cast(ubyte*)_calloc(1, computeSize(f.type, is32Bit));
        }
    }

    private void defaultExceptionHandler()
    {
        auto trace = new StackTrace(currentException.getFrames());
        auto rv = currentException.toRuntimeValue();
        currentException.release();
        setException(null);
        throw new ExecutionException(trace, rv, "Unhandled ial exception");
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
        if (function_.attributes & FunctionAttributes.intrinsic)
        {
            auto fptr = intrinsicFunctions[function_];
            dispatchFFI!true(function_.parameters, function_.returnType, CallingConvention.cdecl, fptr, returnMem, argMem);
            return;
        }


        auto context = new InterpreterContext(function_, this, true, eh);

        context.args = serializeArgs(function_.parameters, argMem);
        context.returnMem = returnMem;
        context.returnContext = currentContext;
        if (context.returnContext)
            context.returnContext.nativeTransition = true;

        // run
        switchToContext(context);
        run();

        // marshal and free up
        foreach (param; function_.parameters)
            _stackAlloc.free(param.type);
    }

    private void detachFromMCIRuntime()
    {
        bool detach;
        auto thisThread = Thread.getThis();

        {
            _attachedThreadsMutex.lock();

            scope (exit)
                _attachedThreadsMutex.unlock();

            if (thisThread in _attachedThreads)
                detach = true;
        }

        if (detach)
        {
            foreach (mod; _loadedModules)
                if (mod.threadExitPoint)
                    execute(mod.threadExitPoint, new NoNullList!RuntimeValue());

            // we need to wait with removing up to this point, otherwise executingthe thredExitPoint will reattach
            _attachedThreadsMutex.lock();

            scope (exit)
                _attachedThreadsMutex.unlock();
            _attachedThreads.remove(thisThread);

            _gc.detach();
        }
    }

    private void detachFromDRuntime()
    {
        GC.disable();
        thread_detachThis();
        rt_moduleTlsDtor();
        GC.enable();
    }

    private void detachFromAllRuntimes()
    {
        detachFromMCIRuntime();
        detachFromDRuntime();
    }

    private void attachToRuntime()
    {
        auto thisThread = Thread.getThis();
        if (!thisThread)
        {
            GC.disable();
            thisThread = thread_attachThis();
            rt_moduleTlsCtor();
            GC.enable();
            registerThreadCleanup(&detachFromAllRuntimes);
            assert(thread_needLock());
        }

        bool attach;

        {
            _attachedThreadsMutex.lock();

            scope (exit)
                _attachedThreadsMutex.unlock();

            if (_attachedThreads.add(thisThread))
            {
                writefln("Attached %s", cast(void*)thisThread);
                attach = true;
            }
        }

        if (attach)
        {
            _gc.attach();

            _loadedModulesMutex.lock();

            scope (exit)
                _loadedModulesMutex.unlock();

            foreach (mod; _loadedModules)
                if (mod.threadEntryPoint)
                    execute(mod.threadEntryPoint, new NoNullList!RuntimeValue());
        }
    }

    private FFIClosure getClosure(T, bool attach = true)(T function_, T source = null, FFIFunction f = null)
    {
        static if (is(T == Function))
        {
            if (auto cache = _closureCache.get(function_))
                return *cache;
        }

        // need a trampoline
        auto returnType = toFFIType(function_.returnType);
        FFIType*[] argTypes;

        static if (is(T == Function))
        {
            auto params = function_.parameters;
            argTypes = new FFIType*[params.count];
            foreach (idx, p; params)
                argTypes[idx] = toFFIType(p.type);
        }
        else
        {
            auto params = function_.parameterTypes;
            argTypes = new FFIType*[params.count];
            foreach (idx, p; params)
                argTypes[idx] = toFFIType(p);
        }

        ExceptionHandler eh;
        static if (longjmpUnwind)
        {
            auto jb = new jmp_buf[1]; // FIXME: dmd has linktime issues with a plain jmp_buf inside a closure
            auto callContext = currentContext;
            eh = delegate void()
            {
                longjmp(jb[0], 1);
            };
        }
        else
        {
            eh = delegate void()
            {
                // we need to abort the current FFI here!
                throw unwindException;
            };
        }

        // careful, as trampoline invocations from native code consume stack until emulation returns.
        // In case a ffi happens during this emulation with noreturn semantics but rather invoking
        // (semantically a jump instruction within the native code) to another trampoline we will
        // leak this D stackframe.
        // But there is not much we can do about this for the moment.
        auto trampoline = delegate void(void* ret, void** args)
        {
            static if (attach)
                attachToRuntime();

            static if (longjmpUnwind)
            {
                if (setjmp(jb[0]) == 1)
                {
                    callContext.unwindException();
                    return;
                }
            }

            static if (is(T == Function))
                runFunction(function_, cast(ubyte*)ret, cast(ubyte**)args, eh);
            else
            {
                auto sourceconv = toFFIConvention(function_.callingConvention);
                auto params = function_.parameterTypes.count;
                auto argsA = new void*[params];
                for (auto i = 0; i < params; i++)
                    argsA[i] = args[i];
                ffiCall(f, returnType, argTypes, ret, argsA, sourceconv);
            }
        };

        auto cconv = toFFIConvention(function_.callingConvention);
        auto closure = ffiClosure(trampoline, returnType, argTypes, cconv);

        static if (is(T == Function))
            _closureCache.add(function_, closure);
        return closure;
    }

    private RuntimeObject* gcallocate(Type t, size_t additionalSize)
    {
        auto typeInfo = getTypeInfo(t, is32Bit);
        auto r = _gc.allocate(typeInfo, additionalSize);
        return r;
    }

    private void gcfree(RuntimeObject* r)
    {
        _gc.free(r);
    }

    private void dispatchFFI(bool isIntrinsic, T, U)(ReadOnlyIndexable!T paramTypes, Type _returnType, CallingConvention convention,
                            FFIFunction entry, ubyte* returnMem, U args)
    {
        auto argCount = paramTypes.count;
        static if (isIntrinsic)
            argCount++;

        auto returnType = toFFIType(_returnType);
        auto argTypes = new FFIType*[argCount];
        auto argMem = new void*[argCount];
        auto cconv = toFFIConvention(convention);

        foreach (idx, p; paramTypes)
        {
            static if (is(T == Parameter) || is(T == RuntimeValue))
                auto t = p.type;
            else
                auto t = p;

            auto i = idx;
            static if (isIntrinsic)
                i++;

            argTypes[i] = toFFIType(t);

            static if (is(typeof(args[i]) == RuntimeValue))
                argMem[i] = args[i].data;
            else argMem[i] = args[i];
        }

        static if (isIntrinsic)
        {
            argTypes[0] = FFIType.ffiPointer;
            argMem[0] = cast(ubyte*)&_vmContext;
        }

        ffiCall(entry, returnType, argTypes, returnMem, argMem, cconv);
    }

    private EntryPoint resolveEntryPoint(FFISignature sig)
    {
        auto key = tuple(sig.library, sig.entryPoint);
        if (auto entry = _ffiEntrypoints.get(key))
            return *entry;

        auto libp = _ffiLibraries.get(sig.library);
        void* lib;
        if (libp)
            lib = *libp;
        else
        {
            // try to load the library
            lib = openLibrary(sig.library);
            if (!lib)
                return null;
            _ffiLibraries.add(sig.library, lib);
        }

        auto entry = getProcedure(lib, sig.entryPoint);
        if (!entry)
            return null;

        _ffiEntrypoints.add(key, entry);
        return entry;
    }

    override void startDebugger(Address address) {}
    override void stopDebugger() {}
}
