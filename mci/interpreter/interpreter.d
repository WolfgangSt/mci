module mci.interpreter.interpreter;

import mci.core.code.modules,
       mci.core.config,
       mci.core.container,
       mci.core.code.functions,
       mci.core.typing.core,
       mci.core.typing.members,
       mci.core.code.opcodes,
       mci.interpreter.exception,
       mci.core.code.instructions,
       mci.vm.memory.base,
       mci.vm.memory.layout,
       core.stdc.string,
       std.stdio;

final class InterpreterContext
{
    public Function fun;
    public BasicBlock block;
    public int instructionIndex;
    public InterpreterContext returnContext;
    public RuntimeObject[] args;
    public int _argIndex;
    private Dictionary!(Register, RuntimeObject) _registerState;
    private GarbageCollector _gc;

    public void gotoBlock(string name)
    {
        block = fun.blocks[name];
        instructionIndex = 0;
    }

    public void gotoEntry()
    {
        gotoBlock("entry");
    }

    public this (Function f, GarbageCollector gc)
    {
        _gc = gc;
        fun = f;

        _registerState = new Dictionary!(Register, RuntimeObject)();
        foreach (namereg; f.registers)
        {
            auto reg = namereg.y;
            auto size = computeSize(reg.type, is32Bit);
            writefln("Allocating %s bytes %s for %s [%s]", size, reg.type.name, reg.name, cast(void*)reg);
            _registerState.add(reg, gc.allocate(reg.type, size));
        }

        gotoEntry();
    }

    public void loadRegister(T)(Register reg, InstructionOperand value)
    {
        auto src = value.peek!T;
        auto dst = cast(T*)_registerState[reg].data;
        *dst = *src;
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
        foreach (r; _registerState.values)
            _gc.free(r);
    }
}


public final class Interpreter
{
    private InterpreterContext _ctx;
	private GarbageCollector _gc;
    private int _numPushs;

    public this(GarbageCollector collector)
    {
		_gc = collector;
    }

    public void interpret(Module mod)
    in
    {
        assert(mod);
    }
    body
    {
        {
            auto main = mod.functions["main"];
            if (checkEntrySignature(main))
                runFunction(main);
        }
    }

    bool checkEntrySignature(Function fun)
    {
        if (!fun.returnType)
            return fun.parameters.empty;
        return false;
    }

    // highlevel D emulation of common ALU instuctions
    private void emulateALUForType(T, string op)(void* target, void* lhs, void* rhs)
    {
         mixin("*cast(T*)target = cast(T)(*cast(T*)lhs " ~ op ~ " *cast(T*)rhs);");
    }

    private void emulateALUFloat(string op)(Instruction inst)
    {
       
    }

    private void emulateALUInt(string op)(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = _ctx.getValue(inst.sourceRegister1).data;
        auto rhsMem = _ctx.getValue(inst.sourceRegister2).data;
        auto dstMem = _ctx.getValue(inst.targetRegister).data;

        if (auto typ = cast(Int8Type)lhsType)
        {
            emulateALUForType!(byte, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt8Type)lhsType)
        {
            emulateALUForType!(ubyte, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int16Type)lhsType)
        {
            emulateALUForType!(short, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt16Type)lhsType)
        {
            emulateALUForType!(ushort, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int32Type)lhsType)
        {
            emulateALUForType!(int, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt32Type)lhsType)
        {
            emulateALUForType!(uint, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int64Type)lhsType)
        {
            emulateALUForType!(long, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt64Type)lhsType)
        {
            emulateALUForType!(ulong, op)(dstMem, lhsMem, rhsMem);
        } else
        {
            throw new InterpreterException("ALU cannot emulated " ~ lhsType.name ~ " yet.");
        }
    }

    private void emulateALU(string op)(Instruction inst)
    {
        auto lhsType = inst.sourceRegister1.type;
        auto lhsMem = _ctx.getValue(inst.sourceRegister1).data;
        auto rhsMem = _ctx.getValue(inst.sourceRegister2).data;
        auto dstMem = _ctx.getValue(inst.targetRegister).data;

        if (auto typ = cast(Float64Type)lhsType)
        {
            emulateALUForType!(double, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Float32Type)lhsType)
        {
            emulateALUForType!(float, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int8Type)lhsType)
        {
            emulateALUForType!(byte, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt8Type)lhsType)
        {
            emulateALUForType!(ubyte, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int16Type)lhsType)
        {
            emulateALUForType!(short, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt16Type)lhsType)
        {
            emulateALUForType!(ushort, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int32Type)lhsType)
        {
            emulateALUForType!(int, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt32Type)lhsType)
        {
            emulateALUForType!(uint, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(Int64Type)lhsType)
        {
            emulateALUForType!(long, op)(dstMem, lhsMem, rhsMem);
        } else if (auto typ = cast(UInt64Type)lhsType)
        {
            emulateALUForType!(ulong, op)(dstMem, lhsMem, rhsMem);
        } else
        {
            throw new InterpreterException("ALU cannot emulated " ~ lhsType.name ~ " yet.");
        }
    }

    private RuntimeObject[] collectArgs()
    {
        if (_numPushs == 0)
            return null;
        
        auto args = new RuntimeObject[_numPushs];
        for (auto i = 0; i < _numPushs; i++)
        {
            auto reg = _ctx.block.instructions[_ctx.instructionIndex - _numPushs - 1 + i].sourceRegister1;
            args[i] = _ctx.getValue(reg);
        }
        _numPushs = 0;
        return args;
    }

    void step()
    {
        auto inst = _ctx.block.instructions[_ctx.instructionIndex++];

        // unroll this using metacode if possible for readability
        switch (inst.opCode.code)
        {
            case OperationCode.nop:
            case OperationCode.comment:
                break;

            case OperationCode.loadI8:
                _ctx.loadRegister!byte(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadUI8:
                _ctx.loadRegister!ubyte(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadI16:
                _ctx.loadRegister!short(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadUI16:
                _ctx.loadRegister!ushort(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadI32:
                _ctx.loadRegister!int(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadUI32:
                _ctx.loadRegister!uint(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadI64:
                _ctx.loadRegister!long(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadUI64:
                _ctx.loadRegister!ulong(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadF32:
                _ctx.loadRegister!float(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.loadF64:
                _ctx.loadRegister!double(inst.targetRegister, inst.operand);                
                break;

            case OperationCode.fieldSet:
                auto dest = inst.sourceRegister1;
                auto source = inst.sourceRegister2;
                auto field = *inst.operand.peek!(Field);
                auto offset = computeOffset(field, is32Bit);
                auto size = computeSize(field.type, is32Bit);
                _ctx.blockCopy(dest, source, offset, 0, size);
                break;

            case OperationCode.fieldGet:
                auto dest = inst.targetRegister;
                auto source = inst.sourceRegister1;
                auto field = *inst.operand.peek!(Field);
                auto offset = computeOffset(field, is32Bit);
                auto size = computeSize(field.type, is32Bit); 
                _ctx.blockCopy(dest, source, 0, offset, size);
                break;
                

            case OperationCode.argPush:
                _numPushs++;
                break; // emulation of push is deferred till call instruction

            case OperationCode.argPop:
                _ctx.popArg(inst.targetRegister);
                break;

            case OperationCode.call:
            case OperationCode.invoke:
                auto target = *inst.operand.peek!Function;
                auto subContext = new InterpreterContext(target, _gc);
                subContext.returnContext = _ctx;
                subContext.args = collectArgs();
                _ctx = subContext; 
                break;

            case OperationCode.callTail:
            case OperationCode.invokeTail:
                _ctx.args = collectArgs();
                _ctx.gotoEntry();
                break;           

            case OperationCode.add:
                emulateALU!("+")(inst);
                break;

            case OperationCode.sub:
                emulateALU!("-")(inst);
                break;

            case OperationCode.mul:
                emulateALU!("*")(inst);
                break;

            case OperationCode.div:
                emulateALU!("/")(inst);
                break;

            case OperationCode.and:
                emulateALUInt!("&")(inst);
                break;

            case OperationCode.or:
                emulateALUInt!("|")(inst);
                break;   

            case OperationCode.xOr:
                emulateALUInt!("^")(inst);
                break;

            case OperationCode.shL:
                emulateALUInt!("<<")(inst);
                break;

            case OperationCode.shR:
                emulateALUInt!(">>")(inst);
                break;

            case OperationCode.return_:
                auto src = _ctx.getValue(inst.sourceRegister1);
                auto oldCtx = _ctx;
                _ctx = _ctx.returnContext;

                auto callInst = _ctx.block.instructions[_ctx.instructionIndex - 1];

                auto dst = _ctx.getValue(callInst.targetRegister);
                auto size = computeSize(callInst.targetRegister.type, is32Bit);
                _ctx.blockCopy(dst, src, 0, 0, size);

                oldCtx.releaseLocals();

                break;

            case OperationCode.leave:
                auto oldCtx = _ctx;
                _ctx = _ctx.returnContext;

                oldCtx.releaseLocals();
                break;


            default:
                throw new InterpreterException("Unsupported opcode: " ~ inst.opCode.name);
        }
    }


    void runFunction(Function fun)
    {
        auto context = new InterpreterContext(fun, _gc);

        _ctx = context;
        while (_ctx)
            step();
    }
}