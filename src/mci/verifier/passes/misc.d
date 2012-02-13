module mci.verifier.passes.misc;

import mci.core.container,
       mci.core.analysis.cfg,
       mci.core.analysis.utilities,
       mci.core.code.functions,
       mci.core.code.instructions,
       mci.core.code.stream,
       mci.core.code.opcodes,
       mci.core.typing.members,
       mci.core.typing.types,
       mci.verifier.base;

public final class EntryVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        if (!function_.blocks.get(entryBlockName))
            error(null, "Functions must have an 'entry' basic block.");
    }
}

public final class FieldStorageVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        foreach (bb; function_.blocks)
        {
            foreach (instr; bb.y.stream)
            {
                if (auto field = instr.operand.peek!Field())
                {
                    if (instr.opCode is opLoadOffset || instr.opCode is opFieldGet ||
                        instr.opCode is opFieldSet || instr.opCode is opFieldAddr)
                    {
                        if (field.storage != FieldStorage.instance)
                            error(instr, "Field reference must have instance storage.");
                    }
                    else if (instr.opCode is opFieldGGet || instr.opCode is opFieldGSet ||
                             instr.opCode is opFieldGAddr)
                    {
                        if (field.storage == FieldStorage.instance)
                            error(instr, "Field reference must have static storage.");
                    }
                }
            }
        }
    }
}

public final class CallSiteCountVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        foreach (bb; function_.blocks)
        {
            size_t pushCount;
            size_t required;

            foreach (instr; bb.y.stream)
            {
                if (instr.opCode is opArgPush)
                {
                    pushCount++;
                    continue;
                }
                else if (isDirectCallSite(instr.opCode))
                    required = (*instr.operand.peek!Function()).parameters.count;
                else if (isIndirectCallSite(instr.opCode))
                    required = (cast(FunctionPointerType)instr.sourceRegister1.type).parameterTypes.count;
                else
                    continue;

                if (pushCount != required)
                    error(instr, "Insufficient 'arg.push' instructions.");

                pushCount = 0;
                required = 0;
            }
        }
    }
}

public final class FunctionArgumentCountVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        auto entry = function_.blocks[entryBlockName];

        if (!containsManagedCode(entry))
            return;

        for (size_t i = 0; i < function_.parameters.count; i++)
        {
            auto instr = entry.stream[i];

            if (instr.opCode !is opArgPop)
                error(instr, "Insufficient 'arg.pop' instructions.");
        }

        auto instr = entry.stream[function_.parameters.count];

        if (instr.opCode is opArgPop)
            error(instr, "Insufficient 'arg.pop' instructions.");
    }
}

public final class PhiRegisterCountVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        foreach (bb; function_.blocks)
            foreach (instr; bb.y.stream)
                if (instr.opCode is opPhi && !instr.operand.peek!(ReadOnlyIndexable!Register)().count)
                    error(instr, "The 'phi' instruction requires one or more registers.");
    }
}

public final class PhiPredecessorVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        foreach (bb; function_.blocks)
        {
            foreach (instr; bb.y.stream)
            {
                if (instr.opCode is opPhi)
                {
                    auto predecessors = getPredecessors(bb.y);
                    auto registers = *instr.operand.peek!(ReadOnlyIndexable!Register)();

                    if (registers.count != predecessors.count)
                        error(instr, "The 'phi' instruction must have as many registers in the selector as its basic block has predecessors.");

                    auto predSet = new HashSet!BasicBlock();

                    foreach (reg; registers)
                    {
                        auto def = first(function_.definitions[reg]);

                        if (!def || !contains(predecessors, def.block))
                            error(instr, "Register '%s' is not defined in any predecessors.", reg);

                        if (!predSet.add(def.block))
                            error(instr, "Register '%s' defined in multiple predecessor basic blocks.", reg);
                    }
                }
            }
        }
    }
}

public final class SSAFormVerifier : CodeVerifier
{
    public override void verify(Function function_)
    {
        if (function_.attributes & FunctionAttributes.ssa)
        {
            foreach (def; function_.definitions)
                if (def.y.count > 1)
                    error(null, "Register '%s' assigned multiple times; invalid SSA form.", def.x);
        }
        else
            if (auto phi = getFirstInstruction(function_, opPhi))
                error(phi, "The 'phi' instruction is not valid in non-SSA functions.");
    }
}
