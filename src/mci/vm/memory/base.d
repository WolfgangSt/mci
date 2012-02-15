module mci.vm.memory.base;

import std.bitmanip,
       mci.core.config,
       mci.core.container,
       mci.core.typing.core,
       mci.core.typing.types,
       mci.vm.memory.info,
       mci.vm.memory.layout;

public final class RuntimeObject
{
    private RuntimeTypeInfo _typeInfo;
    public GCHeader header;

    invariant()
    {
        assert(_typeInfo);
    }

    public this(RuntimeTypeInfo typeInfo)
    in
    {
        assert(typeInfo);
    }
    body
    {
        _typeInfo = typeInfo;
    }

    @property public RuntimeTypeInfo typeInfo()
    out (result)
    {
        assert(result);
    }
    body
    {
        return _typeInfo;
    }

    @property public ubyte* data()
    {
        return cast(ubyte*)this + __traits(classInstanceSize, RuntimeObject);
    }

    public static RuntimeObject fromData(ubyte* data)
    in
    {
        assert(data);
    }
    body
    {
        return cast(RuntimeObject)(data - __traits(classInstanceSize, RuntimeObject));
    }
}

package union GCHeader
{
    // Temporary padding until we make use of this union.
    private size_t bits;
}

private bool isSystemAligned(ubyte* ptr)
{
    return !(cast(size_t)ptr % computeSize(NativeUIntType.instance, is32Bit));
}

public interface GarbageCollector
{
    @property public ulong collections();

    public RuntimeObject allocate(RuntimeTypeInfo type, size_t extraSize = 0)
    in
    {
        assert(type);
    }
    out (result)
    {
        if (result)
            assert(isSystemAligned(cast(ubyte*)result));
    }

    public void free(RuntimeObject data)
    in
    {
        if (data)
            assert(isSystemAligned(cast(ubyte*)data));
    }

    public void addRoot(ubyte* ptr)
    in
    {
        assert(ptr);
        assert(isSystemAligned(ptr));
    }

    public void removeRoot(ubyte* ptr)
    in
    {
        assert(ptr);
        assert(isSystemAligned(ptr));
    }

    public void addRange(ubyte* ptr, size_t words)
    in
    {
        assert(ptr);
        assert(isSystemAligned(ptr));
        assert(words);
    }

    public void removeRange(ubyte* ptr)
    in
    {
        assert(ptr);
        assert(isSystemAligned(ptr));
    }

    public size_t pin(RuntimeObject data)
    in
    {
        assert(data);
        assert(isSystemAligned(cast(ubyte*)data));
    }

    public void unpin(size_t handle);

    public void collect();

    public void minimize();

    public void attach();

    public void detach();

    public void addPressure(size_t amount);

    public void removePressure(size_t amount);
}

public interface GCGeneration
{
    @property public ubyte id();

    @property public ulong collections();

    public void collect();

    public void minimize();
}

public interface GenerationalGarbageCollector : GarbageCollector
{
    @property public ReadOnlyIndexable!GCGeneration generations()
    out (result)
    {
        assert(result);
    }
}

public interface InteractiveGarbageCollector : GarbageCollector
{
    public void addAllocateCallback(void delegate(RuntimeObject) callback)
    in
    {
        assert(callback);
    }

    public void addFreeCallback(void delegate(RuntimeObject) callback)
    in
    {
        assert(callback);
    }
}
