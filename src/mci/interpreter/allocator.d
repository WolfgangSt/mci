module mci.interpreter.allocator;

import mci.core.analysis.utilities,
       mci.core.common,
       mci.core.config,
       mci.core.container,
       mci.core.typing.types,
       mci.vm.memory.base,
       mci.vm.memory.layout,
       std.c.stdlib,
       std.c.string;

private final class StackAllocatorBlock
{
    private size_t _size;
    private size_t _load;
    private ubyte *_mem;
    private StackAllocatorBlock _predecessor;
    private StackAllocator _allocator;

    public this (size_t size, StackAllocator allocator)
    in
    {
        assert(size);
        assert(allocator);
    }
    out
    {
        assert(_mem);
    }
    body
    {
        _allocator = allocator;
        _predecessor = _allocator._topBlock;
        _allocator._topBlock = this;

        _size = size;
        _mem = cast(ubyte*)calloc(size, 1);
        
        _allocator._gc.addRoot(_mem);
    }

    private void releaseBlock()
    {
        _allocator._gc.removeRoot(_mem);
        .free(_mem);
        _size = 0;
        _load = 0;
        _allocator._topBlock = _predecessor;
    }

    public ubyte *allocate(size_t size)
    {
        auto newLoad = _load + size;
        if (newLoad > _size)
        {
            auto newSize = _allocator._defaultAllocationSize;
            newSize = newSize > size ? newSize : size;
            auto newBlock = new StackAllocatorBlock(newSize, _allocator);

            return newBlock.allocate(size);
        }

        auto result = _mem + _load;
        _load = newLoad;

        return result;
    }

    public void free(size_t size)
    {
        if (size >= _load)
        {
            size -= _load;
            releaseBlock();

            // release this block
            if (_predecessor)
                _predecessor.free(size);
            return;
        }

        _load -= size;
        memset(_mem + _load, 0, size);
    }
}

public final class StackAllocator
{
    private StackAllocatorBlock _topBlock;
    private size_t _defaultAllocationSize;
    private GarbageCollector _gc;

    public this(GarbageCollector gc)
    in
    {
        assert(gc);
    }
    body
    {
        _gc = gc;
        _defaultAllocationSize = 0x10000;
    }

    public ubyte* allocate(size_t size)
    {
        if (!_topBlock)
            _topBlock = new StackAllocatorBlock(_defaultAllocationSize, this);
        return _topBlock.allocate(size);
    }

    public void free(size_t size)
    {
        _topBlock.free(size);
    }

    public ubyte* allocate(Type t)
    {
        return allocate(computeSize(t, is32Bit));
    }

    public void free(Type t)
    {
        free(computeSize(t, is32Bit));
    }
}

