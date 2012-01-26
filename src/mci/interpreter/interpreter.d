module mci.interpreter.interpreter;

import core.stdc.string,
       core.memory,
       core.thread,
       ffi,
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

static if (operatingSystem == OperatingSystem.windows)
{
    import std.c.windows.windows;
} 
else
{
    import std.c.linux.linux;
}

final class InterpreterResult
{
    Type resultType;
    ubyte[] result;
}

final class InterpreterContext
{
    public Function fun;
    public BasicBlock block;
    public int instructionIndex;
    public InterpreterContext returnContext;
    public ubyte* returnMem;
    public ubyte*[] args;
    public int _argIndex;
    private Dictionary!(Register, ubyte*, false) _registerState;
    private int _numPushs;
    private Interpreter _interpreter;

    public ReadOnlyIndexable!Type HACK_paramToTypeList(ReadOnlyIndexable!Parameter params)
    {
        NoNullList!Type res = new NoNullList!Type();
        foreach (p; params)
            res.add(p.type);

        return res;
    }

    public void gotoBlock(BasicBlock b)
    {
        block = b;
        instructionIndex = 0;
    }

    public void gotoBlock(string name)
    {
        gotoBlock(fun.blocks[name]);        
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

    public this (Function f, Interpreter interpreter, bool jumpToEntry = true)
    {
        _interpreter = interpreter;
        fun = f;

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
    public ubyte* arrayElement(Register arrayReg, Register indexReg, out uint size)
    {
        auto arrayRto = *cast(RuntimeObject*)getValue(arrayReg);
        auto array = arrayRto.data;
        auto index = *cast(size_t*)getValue(indexReg);

        auto typ = arrayReg.type;

        if (auto vec = cast(VectorType)typ)
            size = computeSize(vec.elementType, is32Bit);
        else
        {
            array += computeSize(NativeUIntType.instance, is32Bit);
            size = computeSize((cast(ArrayType)typ).elementType, is32Bit);
        }

        return array + index * size;
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
            mem = (*cast(RuntimeObject*)mem).data;

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

        auto dst = getValue(reg);
        if (isType!PointerType(reg.type))
            dst = *cast(ubyte**)(dst);
        else 
        {
            dst = (*cast(RuntimeObject*)dst).data;
            if (isType!ArrayType(reg.type))
                dst += computeSize(NativeUIntType.instance, is32Bit);
        }

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


    private void doConv(T1, T2)(T1 *t1, T2 *t2)
    {
        //writefln("conv " ~ T2.stringof ~ " [%s] -> " ~ T1.stringof, *t2);
        *t1 = cast(T1)*t2;
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

            if (isType!FunctionPointerType(t1))
                return binaryDispatcher2!(fun, T2, ubyte*)(t2, null, r1, r2);

            throw new InterpreterException("Dispatcher cannot deal with " ~ t1.name ~ " yet.");
        } else
        {
            enum string code = fun ~ "!(T2, T1)(cast(T2*)r2, cast(T1*)r1);";
            mixin(code);
        }
    }

    // highlevel D emulation of common ALU instuctions
    private void emulateALUForType(T, string op, bool binary, string resultType)(ubyte* target, ubyte* lhs, ubyte* rhs)
    {
        static if (binary)
            enum string code = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")(*cast(T*)lhs " ~ op ~ " *cast(T*)rhs);";
        else
            enum string code = "*cast(" ~ resultType ~ "*)target = cast(" ~ resultType ~ ")(" ~ op ~ " *cast(T*)lhs); ";

        static if (__traits(compiles, { mixin(code); }))
        {
            mixin(code);
            return;
        } 
        else
            throw new InterpreterException("Invalid operation: " ~ op ~ " for " ~ T.stringof);
    }

    private void emulateALU2(string op, bool binary, string resultType="T")(Type lhsType, ubyte* dstMem, ubyte* lhsMem, ubyte* rhsMem)
    {
        if (isType!Int8Type(lhsType))
            return emulateALUForType!(byte, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt8Type(lhsType))
            return emulateALUForType!(ubyte, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!Int16Type(lhsType))
            return emulateALUForType!(short, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt16Type(lhsType))
            return emulateALUForType!(ushort, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!Int32Type(lhsType))
            return emulateALUForType!(int, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt32Type(lhsType))
            return emulateALUForType!(uint, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!Int64Type(lhsType))
            return emulateALUForType!(long, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!UInt64Type(lhsType))
            return emulateALUForType!(ulong, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!Float32Type(lhsType))
            return emulateALUForType!(float, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!Float64Type(lhsType))
            return emulateALUForType!(double, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!NativeUIntType(lhsType))
            return emulateALUForType!(size_t, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        if (isType!NativeIntType(lhsType))
            return emulateALUForType!(isize_t, op, binary, resultType)(dstMem, lhsMem, rhsMem);

        throw new InterpreterException("ALU cannot emulate " ~ op ~ " for " ~ lhsType.name ~ " yet.");
    }


    private void emulateALU(string op, bool binary)(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = getValue(inst.sourceRegister1);
        ubyte* rhsMem = null;
        auto dstMem = getValue(inst.targetRegister);

        static if (binary)
            rhsMem = cast(ubyte*)getValue(inst.sourceRegister2);

        if (auto vec = cast(VectorType)lhsType)
        {
            // all mem locs are pointers
            dstMem = *cast(ubyte**)dstMem;
            lhsMem = *cast(ubyte**)lhsMem;
            static if (binary)
                rhsMem = *cast(ubyte**)rhsMem;

            auto size = computeSize(vec.elementType, is32Bit);
            for (auto i = 0; i < vec.elements; i++)
            {
                emulateALU2!(op, binary)(vec.elementType, dstMem, lhsMem, rhsMem);
                dstMem += size;
                lhsMem += size;
                rhsMem += size;
            }

        } 
        else  
            emulateALU2!(op, binary)(lhsType, dstMem, lhsMem, rhsMem);  
    }

    private void emulateLogic(string op, bool binary)(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = getValue(inst.sourceRegister1);
        ubyte* rhsMem = null;
        auto dstMem = getValue(inst.targetRegister);

        static if (binary)
            rhsMem = cast(ubyte*)getValue(inst.sourceRegister2);

        if (auto vec = cast(VectorType)lhsType)
        {
            // all mem locs are pointers
            dstMem = *cast(ubyte**)dstMem;
            lhsMem = *cast(ubyte**)lhsMem;
            rhsMem = *cast(ubyte**)rhsMem;

            auto size = computeSize(vec.elementType, is32Bit);
            for (auto i = 0; i < vec.elements; i++)
            {
                emulateALU2!(op, binary, "size_t")(vec.elementType, dstMem, lhsMem, rhsMem);
                dstMem += size_t.sizeof;
                lhsMem += size;
                rhsMem += size;
            }

        } 
        else  
            emulateALU2!(op, binary, "size_t")(lhsType, dstMem, lhsMem, rhsMem);  
    }


    private ubyte*[] collectArgs()
    {
        if (_numPushs == 0)
            return null;

        auto args = new ubyte*[_numPushs];
        for (auto i = 0; i < _numPushs; i++)
        {
            auto reg = block.instructions[instructionIndex - _numPushs - 1 + i].sourceRegister1;
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

        _interpreter.dispatchFFI(HACK_paramToTypeList(intrinsic.parameters), intrinsic.returnType, CallingConvention.cdecl, fptr, dst, args); 

        releaseLocals();
        switchToContext(callCtx);
    }


    private void doFFI(Instruction inst)
    {
        auto ffisig = *inst.operand.peek!FFISignature();
        auto fptr = _interpreter.resolveEntryPoint(ffisig);

        if (fptr is null)
            throw new InterpreterException("Cannot resolve export " ~ ffisig.entryPoint ~ " in " ~ ffisig.library);

        // by specification ffi is the only instruction in the block and
        // the FFI signature corresponds to the current methods signature.
        // The calling convention is specified with the FFI

        auto callCtx = returnContext;

        ubyte* dst = null;
        if (fun.returnType)
        {
            auto callInst = callCtx.block.instructions[callCtx.instructionIndex - 1];
            dst = callCtx.getValue(callInst.targetRegister);
        }

        _interpreter.dispatchFFI(HACK_paramToTypeList(fun.parameters), fun.returnType, fun.callingConvention, fptr, dst, args);

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

        _interpreter.dispatchFFI(ffiSig.parameterTypes, ffiSig.returnType, fun.callingConvention, fptr, dst, args);

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
        // Type 5 convert
        // T[E] -> U[E] for any valid T -> U conversion.
        if (auto srcVec = cast(VectorType)(srcType))
        {
            auto dstVec = cast(VectorType)(dstType);

            auto srcRto = *cast(RuntimeObject*)srcMem;
            auto dstRto = *cast(RuntimeObject*)dstMem;

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

        // Type 6 convert (Direct conversion as pointer type)
        // R1(T1, ...) -> R2(U1, ...) for any R1, any R2, and any amount and type of T n and U m.

        // Type 7 convert (Direct conversion as pointer type)
        // R(T1, ...) -> U* for any R, any amount and type of Tn, and any U.

        // Type 8 convert (Direct conversion as pointer type)
        // T* -> R(U1, ...) for any T, any R, and any amount and type of Un.
        binaryDispatcher2!("doConv")(srcType, dstType, srcMem, dstMem);
    }

    @property public bool ready()
    {
        return instructionIndex < block.instructions.count;
    }

    public void step()
    {
        auto inst = block.instructions[instructionIndex++];

        //writefln("%s.%s.%s: %s", block.function_.name, block.name, instructionIndex, inst.toString());

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

            case OperationCode.fieldGGet:
                auto field = *inst.operand.peek!Field();
                auto dest = getValue(inst.targetRegister);
                auto source = _interpreter.getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldGSet:
                auto field = *inst.operand.peek!Field();
                auto source = getValue(inst.sourceRegister1);
                auto dest = _interpreter.getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldGAddr:
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

                auto subContext = new InterpreterContext(target, _interpreter, false);
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
                    auto subContext = new InterpreterContext(target, _interpreter);
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
                emulateALU!("<<", true)(inst);
                break;

            case OperationCode.shR:
                emulateALU!(">>", true)(inst);
                break;

            case OperationCode.return_:
                auto src = getValue(inst.sourceRegister1);

                //auto callInst = returnContext.block.instructions[returnContext.instructionIndex - 1];
                //auto dst = returnContext.getValue(callInst.targetRegister);
                //auto size = computeSize(callInst.targetRegister.type, is32Bit);
                
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
                    auto array = (*cast(RuntimeObject*)getValue(inst.sourceRegister1)).data;
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

                /*
            case OperationCode.memGCAlloc:
            case OperationCode.memSAlloc:
                auto count = *cast(size_t*)getValue(inst.sourceRegister1);
                gcallocate(inst.targetRegister, count);
                break;

            case OperationCode.memGCNew:
            case OperationCode.memSNew:
                gcallocate(inst.targetRegister, 1);
                break;
                */

            case OperationCode.memPin:
            case OperationCode.memUnpin:
                break; // currently the interpreter keeps mem pinned during whole lifetime


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

                /*
            case OperationCode.memGCFree:
                auto rtoDataPointer = getValue(inst.sourceRegister1);
                if (!rtoDataPointer)
                    break;
                auto mem = *cast(ubyte**)rtoDataPointer;
                auto rto = RuntimeObject.fromData(mem);
                _interpreter.gcfree(rto);
                break;
                */

            case OperationCode.memAddr:
                auto mem = getValue(inst.sourceRegister1);
                auto dst = cast(ubyte**)getValue(inst.targetRegister);
                *dst = mem;
                break;

            case OperationCode.cmpEq:
                emulateLogic!("==", true)(inst);
                break;

            case OperationCode.cmpNEq:
                emulateLogic!("!=", true)(inst);
                break;

            case OperationCode.cmpGT:
                emulateLogic!(">", true)(inst);
                break;

            case OperationCode.cmpLT:
                emulateLogic!("<", true)(inst);
                break;

            case OperationCode.cmpGTEq:
                emulateLogic!(">=", true)(inst);
                break;

            case OperationCode.cmpLTEq:
                emulateLogic!("<=", true)(inst);
                break;

            case OperationCode.ffi:
                doFFI(inst);
                break;

            case OperationCode.phi:
                throw new InterpreterException("Phi is invalid in executable ial");

            case OperationCode.exThrow:
            case OperationCode.exTry:
            case OperationCode.exHandle:
            case OperationCode.exEnd:
                throw new InterpreterException("Unsupported opcode: " ~ inst.opCode.name);
        }
        
        //GC.collect();
    }
}


////////////////////////////////////////////////////////////////////////////////
// shared data

private __gshared Dictionary!(Type, FFIType*, false) ffiStructTypeCache;
private Dictionary!(Tuple!(Interpreter, Field), ubyte*, false) tlsGlobals;


shared static this() 
{
    ffiStructTypeCache = new Dictionary!(Type, FFIType*, false);
}

static this()
{    
    tlsGlobals = new Dictionary!(Tuple!(Interpreter, Field), ubyte*, false);
}

static ~this()
{
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

private void step()
{
    currentContext.step();
}

private void run()
{
    while (currentContext && currentContext.ready)
        currentContext.step();
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


    private ubyte*[] serializeArgs(ReadOnlyIndexable!Parameter params, ubyte** argMem)
    {
        auto args = new ubyte*[params.count];

        foreach (idx, p; params)
        {
            auto size = computeSize(p.type, is32Bit);
            auto arg = cast(ubyte*)_calloc(1, size);
            memcpy(arg, argMem[idx], size);
            args[idx] = arg;
        }

        return args;
    }

    // TODO: use returnMem directly once everything works again
    private void runFunction(Function function_, ubyte *returnMem, ubyte** argMem)
    {
        auto context = new InterpreterContext(function_, this);

        context.args = serializeArgs(function_.parameters, argMem);

        // if data is to be returned, allocate mem
        auto returnType = function_.returnType;
        uint returnSize = 0;
        if (returnType)
        {
            returnSize = computeSize(returnType, is32Bit);
            context.returnMem = cast(ubyte*)_calloc(1, returnSize);
        }

        // run
        switchToContext(context);
        run();

        // marshal and free up
        foreach (arg; context.args)
            _free(arg);

        if (returnType)
        {
            memcpy(returnMem, context.returnMem, returnSize);
            _free(context.returnMem);
        }
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
          
            runFunction(function_, cast(ubyte*)ret, cast(ubyte**)args);
            writefln("Trampoline returning to native code");
        };

        auto cconv = toFFIConvention(function_.callingConvention);
        auto closure = ffiClosure(trampoline, returnType, argTypes, cconv);

        _closureCache.add(function_, closure);
        return closure;
    }


    public RuntimeObject gcallocate(Type t, size_t additionalSize)
    {
        auto typeInfo = getTypeInfo(t, is32Bit);
        auto r = _gc.allocate(typeInfo, additionalSize);
        _gc.pin(r);
        return r;
    }

    public void gcfree(RuntimeObject r)
    {
        _gc.free(r);
    }

    public FFIFunction resolveEntryPoint(FFISignature sig)
    {
        static if (operatingSystem == OperatingSystem.windows)
        {
            import std.c.windows.windows;

            auto libName = toUTFz!(const(wchar)*)(sig.library);
            auto impName = toUTFz!(const(char)*)(sig.entryPoint);
            // try GetModuleHandle first
            auto lib = GetModuleHandleW(libName);
            if (!lib)
                lib = LoadLibraryW(libName);
            return cast(FFIFunction)GetProcAddress(lib, impName);
        }
        else
        {
            auto libName = toUTFz!(const(char)*)(sig.library);
            auto impName = toUTFz!(const(char)*)(sig.entryPoint);
            //auto lib = dlopen(libName, RTLD_NOLOAD);

            //if (lib is null)
            auto    lib = dlopen(libName, RTLD_LOCAL);

            return cast(FFIFunction)dlsym(lib, impName);
        }
    }

    private Function toFunction(ubyte *mem)
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
                            FFIFunction entry, ubyte *returnMem, ubyte*[] args)
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
        auto context = new InterpreterContext(fun, this);
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
        } else
            writeln("The program quitted without return value.");
        
        return result;
    }
}
