module mci.interpreter.interpreter;

import core.stdc.string,
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
       mci.interpreter.exception,
       mci.core.code.instructions,
       mci.vm.intrinsics.declarations,
       mci.vm.memory.base,
       mci.vm.memory.layout,
       mci.vm.memory.prettyprint,
       std.c.stdlib,
       std.stdio,
       std.string,
       std.traits,
       std.utf;

extern (C) void* memcpy(void*, const void*, size_t);
extern (C) void rt_moduleTlsCtor();

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
    RuntimeObject result;
}

final class InterpreterContext
{
    public Function fun;
    public BasicBlock block;
    public int instructionIndex;
    public InterpreterContext returnContext;
    public RuntimeObject returnMem;
    public RuntimeObject[] args;
    public int _argIndex;
    private Dictionary!(Register, RuntimeObject) _registerState;
    private int _numPushs;
    private Interpreter _interpreter;


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

    private void allocateVectorMem(Register reg)
    {
        if (auto vec = cast(VectorType)reg.type)
        {
            // allocate vector data as well
            auto mem = getValue(reg);
            auto vecsize = computeSize(vec.elementType, is32Bit) * vec.elements;
            //writefln("  Allocating %s additional bytes for data", vecsize);
            *cast(ubyte**)mem.data = (new ubyte[vecsize]).ptr;
        }
    }

    public this (Function f, Interpreter interpreter, bool jumpToEntry = true)
    {
        _interpreter = interpreter;
        fun = f;

        _registerState = new Dictionary!(Register, RuntimeObject)();
        foreach (namereg; f.registers)
        {
            auto reg = namereg.y;
            auto size = computeSize(reg.type, is32Bit);
            //writefln("Allocating %s bytes %s for %s [%s]", size, reg.type.name, reg.name, cast(void*)reg);

            auto mem = _interpreter.gcallocate(reg.type, size);
            _registerState.add(reg, mem);

            allocateVectorMem(reg);
        }

        if (jumpToEntry)
            gotoEntry();
    }

    public ubyte* arrayElement(Register arrayReg, Register indexReg, out uint size)
    {
        auto array = *cast(ubyte**)getValue(arrayReg).data;
        auto index = *cast(size_t*)getValue(indexReg).data;

        auto typ = arrayReg.type;

        if (auto vec = cast(VectorType)typ)
            size = computeSize(vec.elementType, is32Bit);
        else
            size = computeSize((cast(ArrayType)typ).elementType, is32Bit);

        return array + index * size;
    }

    public void loadRegister(T)(Register reg, InstructionOperand value)
    {
        auto src = value.peek!T();
        auto dst = cast(T*)_registerState[reg].data;
        *dst = *src;
    }

    public void loadArray(T)(Register reg, InstructionOperand value)
    {
        auto data = *value.peek!(ReadOnlyIndexable!T)();
        gcallocate(reg, data.count);
        auto mem = *cast(T**)(getValue(reg).data);
        foreach (idx, value; data)
            mem[idx] = value;
    }

    public void blockCopy(RuntimeObject destination, RuntimeObject source, 
                          int destinationOffset, int sourceOffset, int size)
    {
        auto src = cast(ubyte*)source.data + sourceOffset;
        auto dst = cast(ubyte*)destination.data + destinationOffset;
        memcpy(dst, src, size);
    }

    public void blockCopy(Register destination, Register source, 
                          int destinationOffset, int sourceOffset, int size)
    {
        blockCopy(_registerState[destination], _registerState[source],
                  destinationOffset, sourceOffset, size);
    }

    public RuntimeObject getValue(Register reg)
    {
        return _registerState[reg];
    }

    public void popArg(Register target)
    {
        blockCopy(_registerState[target], args[_argIndex++], 0, 0, computeSize(target.type, is32Bit));
    }

    public void releaseLocals()
    {
        foreach (r; _registerState.values())
            _interpreter.gcfree(r);
    }

    struct NullType {};

    private void unaryDispatcher2(string fun, T = NullType)(Register r, T userData)
    {
        auto mem = getValue(r).data;
        auto typ = r.type;

        static if (is(T == NullType))
        {
            enum string arg = "";
            enum string pass = "";
        }
        else 
        {
            enum string arg = "T, ";
            enum string pass = ", userData";
        }

        enum string codeI8 = fun ~ "!(" ~ arg ~ "byte)(cast(byte*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeI8); }))
        {
            if (isType!Int8Type(typ))
            {
                mixin (codeI8);
                return;
            }
        }

        enum string codeUI8 = fun ~ "!(" ~ arg ~ "ubyte)(cast(ubyte*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeUI8); }))
        {
            if (isType!UInt8Type(typ))
            {
                mixin (codeUI8);
                return;
            }
        }

        enum string codeI16 = fun ~ "!(" ~ arg ~ "short)(cast(short*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeI16); }))
        {
            if (isType!Int16Type(typ))
            {
                mixin (codeI16);
                return;
            }
        }

        enum string codeUI16 = fun ~ "!(" ~ arg ~ "ushort)(cast(ushort*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeUI16); }))
        {
            if (isType!UInt16Type(typ))
            {
                mixin (codeUI16);
                return;
            }
        }

        enum string codeI32 = fun ~ "!(" ~ arg ~ "int)(cast(int*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeI32); }))
        {
            if (isType!Int32Type(typ))
            {
                mixin (codeI32);
                return;
            }
        }

        enum string codeUI32 = fun ~ "!(" ~ arg ~ "uint)(cast(uint*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeUI32); }))
        {
            if (isType!UInt32Type(typ))
            {
                mixin (codeUI32);
                return;
            }
        }

        enum string codeI64 = fun ~ "!(" ~ arg ~ "long)(cast(long*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeI64); }))
        {
            if (isType!Int64Type(typ))
            {
                mixin (codeI64);
                return;
            }
        }

        enum string codeUI64 = fun ~ "!(" ~ arg ~ "ulong)(cast(ulong*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeUI64); }))
        {
            if (isType!UInt64Type(typ))
            {
                mixin (codeUI64);
                return;
            }
        }

        enum string codeFloat32 = fun ~ "!(" ~ arg ~ "float)(cast(float*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeFloat32); }))
        {
            if (isType!Float32Type(typ))
            {
                mixin (codeFloat32);
                return;
            }
        }

        enum string codeFloat64 = fun ~ "!(" ~ arg ~ "double)(cast(double*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeFloat64); }))
        {
            if (isType!Float64Type(typ))
            {
                mixin (codeFloat64);
                return;
            }
        }

        enum string codeNativeUInt = fun ~ "!(" ~ arg ~ "size_t)(cast(size_t*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeNativeUInt); }))
        {
            if (isType!NativeUIntType(typ))
            {
                mixin (codeNativeUInt);
                return;
            }
        }

        enum string codeNativeInt = fun ~ "!(" ~ arg ~ "isize_t)(cast(isize_t*)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codeNativeInt); }))
        {
            if (isType!NativeIntType(typ))
            {
                mixin (codeNativeUInt);
                return;
            }
        }

        enum string codePointer = fun ~ "!(" ~ arg ~ "void*)(cast(void**)mem" ~ pass ~ ");";
        static if (__traits(compiles, { mixin(codePointer); }))
        {
            if (isType!PointerType(typ))
            {
                mixin (codePointer);
                return;
            }
        }

        throw new InterpreterException("Dispatcher cannot deal with " ~ typ.name ~ " yet.");
    }

    private void unaryDispatcher(string fun)(Register r)
    {
        unaryDispatcher2!fun(r, NullType());
    }

    private struct BinaryContext(string fun)
    {
        enum string f = fun;
        Register r2;
    }

    private struct BinaryResult(string fun, T)
    {
        enum string f = fun;
        T* t;
    }

    private void binaryWrapper2(Ctx, T)(T* t, Ctx res)
    {
        mixin(Ctx.f ~ "!(pointerTarget!(typeof(res.t)), T)(res.t, t);" );
    }

    private void binaryWrapper(Ctx, T)(T* t, Ctx r2) 
    {
        BinaryResult!(Ctx.f, T) res;
        res.t = t;
        unaryDispatcher2!("binaryWrapper2", typeof(res))(r2.r2, res);
    } 

    private void binaryDispatcher(string fun)(Register r1, Register r2)
    {
        BinaryContext!fun ctx;
        ctx.r2 = r2;
        unaryDispatcher2!("binaryWrapper", typeof(ctx))(r1, ctx);
    }


    private void doConv(T1, T2)(T1 *t1, T2 *t2)
    {
        //writefln("conv " ~ T2.stringof ~ " [%s] -> " ~ T1.stringof, *t2);
        *t1 = cast(T1)*t2;
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
        auto lhsMem = getValue(inst.sourceRegister1).data;
        ubyte* rhsMem = null;
        auto dstMem = getValue(inst.targetRegister).data;

        static if (binary)
            rhsMem = cast(ubyte*)getValue(inst.sourceRegister2).data;

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

        } else  
            emulateALU2!(op, binary)(lhsType, dstMem, lhsMem, rhsMem);  
    }

    private void emulateLogic(string op, bool binary)(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = getValue(inst.sourceRegister1).data;
        ubyte* rhsMem = null;
        auto dstMem = getValue(inst.targetRegister).data;

        static if (binary)
            rhsMem = cast(ubyte*)getValue(inst.sourceRegister2).data;

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

        } else  
            emulateALU2!(op, binary, "size_t")(lhsType, dstMem, lhsMem, rhsMem);  
    }


    private RuntimeObject[] collectArgs()
    {
        if (_numPushs == 0)
            return null;

        auto args = new RuntimeObject[_numPushs];
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
            dst = callCtx.getValue(inst.targetRegister).data;

        auto fptr = intrinsicFunctions[intrinsic];

        _interpreter.dispatchFFI(intrinsic, CallingConvention.cdecl, fptr, dst, args); 

        releaseLocals();
        switchToContext(callCtx);
    }


    private void doFFI(Instruction inst)
    {
        auto ffisig = *inst.operand.peek!FFISignature();
        auto fptr = _interpreter.resolveEntrypoint(ffisig);

        if (fptr is null)
            throw new InterpreterException("Cannot resolve export " ~ ffisig.entryPoint ~ " in " ~ ffisig.library);

        // by specification ffi is the only instruction in the block and
        // the FFI signature corresponds to the current methods signature.
        // The calling convention is specified with the FFI

        auto callCtx = returnContext;

        ubyte *dst = null;
        if (fun.returnType)
        {
            auto callInst = callCtx.block.instructions[callCtx.instructionIndex - 1];
            dst = callCtx.getValue(callInst.targetRegister).data;
        }

        _interpreter.dispatchFFI(fun, fun.callingConvention, fptr, dst, args);  

        releaseLocals();
        switchToContext(callCtx);
    }


    private void allocate(Register target, size_t count)
    {
        if (auto typ = (cast(PointerType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target).data;
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = cast(ubyte*)calloc(count, elementSize);
            *dst = mem;

            return;
        }

        if (auto typ = (cast(ArrayType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target).data;
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = cast(ubyte*)calloc(count, elementSize);
            *dst = mem;

            return;
        }

        throw new InterpreterException("Unsupported allocate target: " ~ target.name);
    }

    private void gcallocate(Register target, size_t count)
    {
        if (auto typ = (cast(PointerType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target).data;
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = _interpreter.gcallocate(elementType, count * elementSize);
            *dst = mem.data;

            return;
        }

        if (auto typ = (cast(ArrayType)target.type))
        {
            auto dst = cast(ubyte**)getValue(target).data;
            auto elementType = typ.elementType;
            auto elementSize = computeSize(elementType, is32Bit);
            auto mem = _interpreter.gcallocate(elementType, count * elementSize);
            *dst = mem.data;

            return;
        }

        throw new InterpreterException("Unsupported allocate target: " ~ target.name);
    }

    @property public bool ready()
    {
        return instructionIndex < block.instructions.count;
    }

    public void step()
    {
        auto inst = block.instructions[instructionIndex++];

        //writefln("%s.%s: %s", block.name, instructionIndex, inst.toString());

        // unroll this using metacode if possible for readability
        switch (inst.opCode.code)
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
                memset(obj.data, 0, sz);
                break;

            case OperationCode.loadSize:
                auto size = computeSize(*inst.operand.peek!Type(), is32Bit);
                *cast(size_t*)getValue(inst.targetRegister).data = size;
                break;

            //case OperationCode.loadAlign:
            //    auto alignment = computeAlignment(*inst.operand.peek!Type(), is32Bit);
            //    *cast(size_t*)getValue(inst.targetRegister).data = alignment;
            //    break;

            case OperationCode.loadOffset:
                auto offset = computeOffset(*inst.operand.peek!Field(), is32Bit);
                *cast(size_t*)getValue(inst.targetRegister).data = offset;
                break;

            case OperationCode.fieldGet:
                auto dest = getValue(inst.targetRegister).data;
                auto source = getValue(inst.sourceRegister1).data;
                auto field = *inst.operand.peek!Field();
                auto offset = computeOffset(field, is32Bit);
                auto size = computeSize(field.type, is32Bit); 

                if (isType!PointerType(inst.sourceRegister1.type))
                    source = *cast(ubyte**)source;

                source += offset;
                memcpy(dest, source, size);

                break;

            case OperationCode.fieldSet:
                auto dest = getValue(inst.sourceRegister1).data;
                auto source = getValue(inst.sourceRegister2).data;
                auto field = *inst.operand.peek!Field();
                auto offset = computeOffset(field, is32Bit);
                auto size = computeSize(field.type, is32Bit);

                if (isType!PointerType(inst.sourceRegister1.type))
                    dest = *cast(ubyte**)dest;

                dest += offset;
                memcpy(dest, source, size);

                break;

            case OperationCode.fieldAddr:
                auto dest = getValue(inst.targetRegister).data;
                auto source = getValue(inst.sourceRegister1).data;
                auto field = *inst.operand.peek!Field();
                auto offset = computeOffset(field, is32Bit);
                auto size = computeSize(field.type, is32Bit); 

                if (isType!PointerType(inst.sourceRegister1.type))
                    source = *cast(ubyte**)source;

                source += offset;
                *cast(ubyte**)dest = source;

                break;

            case OperationCode.fieldGGet:
                auto field = *inst.operand.peek!Field();
                auto dest = getValue(inst.targetRegister).data;
                auto source = getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldGSet:
                auto field = *inst.operand.peek!Field();
                auto source = getValue(inst.sourceRegister1).data;
                auto dest = getGlobal(field);
                auto size = computeSize(field.type, is32Bit); 
                memcpy(dest, source, size);
                break;

            case OperationCode.fieldGAddr:
                auto field = *inst.operand.peek!Field();
                auto dest = getValue(inst.targetRegister).data;
                auto source = getGlobal(field);
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
                auto funPtr = getValue(inst.sourceRegister1).data;

                // TODO: impl this check as soon zor added the functionality
                //if (funType.callingConvention == CallingConvention.queueCall)
                if (true)
                {
                    auto target = *cast(Function*)funPtr;
                    auto subContext = new InterpreterContext(target, _interpreter);
                    subContext.returnContext = this;
                    subContext.args = collectArgs();
                    switchToContext(subContext);
                } else
                    throw new InterpreterException("Foreign Function Interfacing not supported yet");
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
                
                auto size = computeSize(returnMem.type, is32Bit);
                blockCopy(returnMem, src, 0, 0, size);

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
                    writeln( prettyPrint(arg.type, is32Bit, getValue(arg).data, arg.name ) );
                } else
                {
                    // TODO: 
                    // handle conversion from array to ptr
                    // handle conversion from ptr to array


                    // Type 5 & 6 convert
                    // T* -> T[] for any T.
                    // T[] -> T* for any T.
                    if ((isType!(PointerType)(inst.sourceRegister1.type) && isType!(ArrayType)(inst.targetRegister.type)) || 
                        (isType!(ArrayType)(inst.sourceRegister1.type) && isType!(PointerType)(inst.targetRegister.type)))
                    {
                        // plain copy
                        auto dst = getValue(inst.targetRegister).data;
                        auto src = getValue(inst.sourceRegister1).data;
                        *cast(ubyte**)dst = *cast(ubyte**)src;
                        break;
                    }

                    // Type 7 convert (TODO)
                    // T[E] -> U[E] for any valid T -> U conversion.

                    // Type 8 convert (TODO)
                    // R1(T1, ...) -> R2(U1, ...) for any R1, any R2, and any amount and type of T n and U m.

                    // Type 10 convert (TODO)
                    // T* -> R(U1, ...) for any T, any R, and any amount and type of Un.


                    // Direct conversions

                    // Type 1 convert
                    // T -> U for any primitives T and U (int8, uint8, int16, uint16, int32, uint32, int64, uint64, int, uint, float32, and float64).

                    // Type 2 convert
                    // T* -> uint or int for any T.

                    // Type 3 convert
                    // uint or int -> T* for any T.

                    // Type 4 convert
                    // T* -> U* for any T and any U.

                    // Type 9 convert
                    // R(T1, ...) -> U* for any R, any amount and type of Tn, and any U.
                    binaryDispatcher!"doConv"(inst.targetRegister, inst.sourceRegister1);
                }
                break;

            case OperationCode.arraySet:
                {
                    auto src   = getValue(inst.sourceRegister3).data;
                    uint size;
                    auto dst = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    memcpy(dst, src, size);
                    break;
                }

            case OperationCode.arrayGet:
                {
                    auto dst   = getValue(inst.targetRegister).data;
                    uint size;
                    auto src = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    memcpy(dst, src, size);
                    break;
                }

            case OperationCode.arrayAddr:
                {
                    auto dst   = getValue(inst.targetRegister).data;
                    uint size;
                    auto src = arrayElement(inst.sourceRegister1, inst.sourceRegister2, size);

                    *cast(ubyte**)dst = src;
                    break;
                }

            case OperationCode.jump:
                gotoBlock(*inst.operand.peek!BasicBlock());
                break;

            case OperationCode.jumpCond:
                auto value = *cast(size_t*)getValue(inst.sourceRegister1).data;
                auto goals = *inst.operand.peek!(Tuple!(BasicBlock, BasicBlock))();
                if (value != 0)
                    gotoBlock(goals.x);
                else 
                    gotoBlock(goals.y);
                break;

            case OperationCode.memAlloc:
                auto count = *cast(size_t*)getValue(inst.sourceRegister1).data;
                allocate(inst.targetRegister, count);
                break;

            case OperationCode.memNew:
                allocate(inst.targetRegister, 1);
                allocateVectorMem(inst.targetRegister);
                break;

            case OperationCode.memGCAlloc:
            case OperationCode.memSAlloc:
                auto count = *cast(size_t*)getValue(inst.sourceRegister1).data;
                gcallocate(inst.targetRegister, count);
                break;

            case OperationCode.memGCNew:
            case OperationCode.memSNew:
                gcallocate(inst.targetRegister, 1);
                allocateVectorMem(inst.targetRegister);
                break;


            case OperationCode.memSet:
                auto size = computeSize(inst.sourceRegister2.type, is32Bit);
                auto dst = *cast(ubyte**)getValue(inst.sourceRegister1).data;
                auto src = getValue(inst.sourceRegister2).data;
                memcpy(dst, src, size);

                break;

            case OperationCode.memGet:
                auto size = computeSize(inst.targetRegister.type, is32Bit);
                auto src = *cast(ubyte**)getValue(inst.sourceRegister1).data;
                auto dst = getValue(inst.targetRegister).data;
                memcpy(dst, src, size);
                break;

            case OperationCode.memFree:
                auto mem = *cast(ubyte**)getValue(inst.sourceRegister1).data;
                free(mem);
                break;

            case OperationCode.memGCFree:
                auto mem = *cast(ubyte**)getValue(inst.sourceRegister1).data;
                auto rto = RuntimeObject.fromData(mem);
                _interpreter.gcfree(rto);
                break;

            case OperationCode.memAddr:
                auto mem = getValue(inst.sourceRegister1).data;
                auto dst = cast(ubyte**)getValue(inst.targetRegister).data;
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

            default:
                throw new InterpreterException("Unsupported opcode: " ~ inst.opCode.name);
        }
    }
}


////////////////////////////////////////////////////////////////////////////////
// shared data

private __gshared Dictionary!(Type, FFIType*) ffiStructTypeCache;
private __gshared Dictionary!(Field, ubyte*) globals;
private Dictionary!(Field, ubyte*) tlsGlobals;


shared static this() 
{
    ffiStructTypeCache = new Dictionary!(Type, FFIType*);
    globals = new Dictionary!(Field, ubyte*);
}

static this()
{    
    tlsGlobals = new Dictionary!(Field, ubyte*);
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

ubyte* getGlobal(Field f)
{
    if (f.storage == FieldStorage.thread)
    {
        if (auto cache = tlsGlobals.get(f))
            return *cache;

        return tlsGlobals[f] = cast(ubyte*)calloc(1, computeSize(f.type, is32Bit));
    } 
    else synchronized(globals)
    {
        if (auto cache = globals.get(f))
            return *cache;

        return globals[f] = cast(ubyte*)calloc(1, computeSize(f.type, is32Bit));
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
    private Dictionary!(Function, FFIClosure) _closureCache;
    

    public this(GarbageCollector collector)
    {
        _gc = collector;
        _closureCache = new Dictionary!(Function, FFIClosure);
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

    private RuntimeObject[] serializeArgs(ReadOnlyIndexable!Parameter params, ubyte** argMem)
    {
        auto args = new RuntimeObject[params.count];

        foreach (idx, p; params)
        {
            auto size = computeSize(p.type, is32Bit);
            auto arg = gcallocate(p.type, size);
            memcpy(arg.data, argMem[idx], size);
            args[idx] = arg;
        }

        return args;
    }

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
            context.returnMem = gcallocate(returnType, returnSize);
        }

        // run
        switchToContext(context);
        run();

        // marshal and free up
        foreach (arg; context.args)
            gcfree(arg);

        if (returnType)
        {
            memcpy(returnMem, context.returnMem.data, returnSize);
            gcfree(context.returnMem);
        }

        context.releaseLocals();
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


        // careful trampolines actually consume stack
        auto trampoline = delegate void(void* ret, void** args) 
        { 
            if (!tlsGlobals)
            {
                thread_attachThis();
                rt_moduleTlsCtor();
            }
          
            runFunction(function_, cast(ubyte*)ret, cast(ubyte**)args);
        };

        auto cconv = toFFIConvention(function_.callingConvention);
        auto closure = ffiClosure(trampoline, returnType, argTypes, cconv);

        _closureCache.add(function_, closure);
        return closure;
    }


    public RuntimeObject gcallocate(Type t, size_t size)
    {
        return _gc.allocate(t, size);
    }

    public void gcfree(RuntimeObject r)
    {
        _gc.free(r);
    }

    public FFIFunction resolveEntrypoint(FFISignature sig)
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
        auto fun = cast(Function)(*cast(ubyte**)mem);

        // TODO:
        // unfortunatley D wont validate the above cast, so we have to do this ourself here
        // by walking over all currently loaded functions.
        // at the moment we assume it always is a Function
        //
        // use the XRefVisitor to collect all funcs during startup and check fun against them
        
        return fun;
    }


    private ubyte* getParamMem(ubyte* mem, Type t)
    {
        if (auto fptr = cast(FunctionPointerType)t)
        {
            // the supplied argument is either a native function pointer to a function
            // or a pointer to a Function object in the latter case we need to
            // create a trampoline to the emulator

            if (auto fun = toFunction(mem))
                return cast(ubyte*)getClosure(fun).function_;
            
            return mem;
        }
        return mem;
    }

    public void dispatchFFI(Function fun, CallingConvention convention, FFIFunction entry, ubyte *returnMem, RuntimeObject[] args)
    {
        auto params = fun.parameters;
        auto returnType = toFFIType(fun.returnType);
        auto argTypes = new FFIType*[params.count];
        auto argMem = new void*[params.count];
        auto cconv = toFFIConvention(convention);

        foreach (idx, p; params)
        {
            argTypes[idx] = toFFIType(p.type);
            argMem[idx] = getParamMem(args[idx].data, p.type);
        }

        ffiCall(entry, returnType, argTypes, returnMem, argMem, cconv); 
    }

    InterpreterResult runFunction(Function fun)
    {
        auto context = new InterpreterContext(fun, this);
        auto returnType = fun.returnType;
        if (returnType)
            context.returnMem = gcallocate(returnType, computeSize(returnType, is32Bit));
        switchToContext(context);
        run();

        auto result = new InterpreterResult();
        result.resultType = returnType;
        result.result = context.returnMem;

        if (returnType)
        {
            writeln("The program quitted with:");
            writeln( prettyPrint( result.resultType, is32Bit, result.result.data, "(return value)" ) );
        }
        
        return result;
    }
}
