module mci.vm.memory.entrypoint;

import  mci.core.code.functions,
        mci.core.common,
        mci.core.config,
        std.string,
        std.utf;

static if (operatingSystem != OperatingSystem.windows)
{
    import std.c.linux.linux,
           std.path; 
}

alias void function() EntryPoint;

public EntryPoint resolveEntryPoint(FFISignature sig)
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
        return cast(EntryPoint)GetProcAddress(lib, impName);
    }
    else
    {
        const(char)* libName;
        void* lib = null;

        //TODO: try to probe
        //auto lib = dlopen(libName, RTLD_NOLOAD);

        if (isValidFilename(sig.library))
        {
            // try loading locally first
            libName = toUTFz!(const(char)*)("./" ~ sig.library);
            lib = dlopen(libName, RTLD_LAZY);
        }

        if (lib is null)
        {
            libName = toUTFz!(const(char)*)(sig.library);
            lib = dlopen(libName, RTLD_LAZY);
        }

        if (lib is null)
            return null;
        
        auto impName = toUTFz!(const(char)*)(sig.entryPoint);
        return cast(EntryPoint)dlsym(lib, impName);
    }
}
