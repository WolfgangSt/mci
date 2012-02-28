module mci.linker.clash;

import std.string,
       mci.core.code.modules,
       mci.core.typing.types,
       mci.linker.exception;

public enum NameType : ubyte
{
    type,
    function_,
}

public interface NameClashResolver
{
    public string resolveNameClash(Module module_, NameType type, string name, string fullName1, string fullName2)
    in
    {
        assert(module_);
        assert(name);
        assert(fullName1);
        assert(fullName2);
    }
    out (result)
    {
        assert(result);
    }
}

public final class ErrorResolver : NameClashResolver
{
    public string resolveNameClash(Module module_, NameType type, string name, string fullName1, string fullName2)
    {
        string typeStr;

        final switch (type)
        {
            case NameType.type:
                typeStr = "type";
                break;
            case NameType.function_:
                typeStr = "function";
                break;
        }

        throw new LinkerException(format("Clash between %s names %s and %s.", typeStr, fullName1, fullName2));
    }
}

public final class RenameResolver : NameClashResolver
{
    public string resolveNameClash(Module module_, NameType type, string name, string fullName1, string fullName2)
    {
        auto resolvedName = format("%s_%s", module_.name, name);

        final switch (type)
        {
            case NameType.type:
                while (module_.types.get(resolvedName))
                    resolvedName ~= "_T";

                break;
            case NameType.function_:
                while (module_.functions.get(resolvedName))
                    resolvedName ~= "_F";

                break;
        }

        return resolvedName;
    }
}
