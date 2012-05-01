module mci.interpreter.allocator;

import mci.core.analysis.utilities,
       mci.core.common,
       mci.core.config,
       mci.core.container,
       mci.core.typing.core,
       mci.core.typing.types,
       mci.vm.memory.base,
       mci.vm.memory.layout,
       std.c.stdlib,
       std.c.string;


private __gshared size_t _wordSize;

shared static this()
{
    _wordSize = computeSize(NativeUIntType.instance, is32Bit);
}

private size_t doAlign(size_t value)
{
    return (value + _wordSize -1) & -_wordSize;
}

private final class StackAllocatorBlock
{
    private size_t _size;
    private size_t _sizeInWords;
    private size_t _load;
    private ubyte* _mem;
    private StackAllocatorBlock _predecessor;
    private StackAllocator _allocator;

    public this (size_t sizeInWords, StackAllocator allocator)
    in
    {
        assert(sizeInWords);
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

        _size = sizeInWords * _wordSize;
        _mem = cast(ubyte*)calloc(_size, 1);
        
        _sizeInWords = sizeInWords;
        _allocator._gc.addRange(cast(RuntimeObject**)_mem, sizeInWords);
    }

    private void releaseBlock()
    {
        _allocator._gc.removeRange(cast(RuntimeObject**)_mem, _sizeInWords);
        .free(_mem);
        _size = 0;
        _load = 0;
        _allocator._topBlock = _predecessor;
    }

    public ubyte* allocate(size_t size)
    {
        auto newLoad = _load + size;
        if (newLoad > _size)
        {
            auto newSizeInWords = _allocator._defaultAllocationSize;
            auto requestedWords = (size + _wordSize - 1) / _wordSize;
            newSizeInWords = newSizeInWords > requestedWords ? newSizeInWords : requestedWords;
            auto newBlock = new StackAllocatorBlock(newSizeInWords, _allocator);

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
        _defaultAllocationSize = 0x10000; // in machine words
    }

    public ubyte* allocate(size_t size)
    {
        size = doAlign(size);
        if (!_topBlock)
            _topBlock = new StackAllocatorBlock(_defaultAllocationSize, this);
        return _topBlock.allocate(size);
    }

    public void free(size_t size)
    {
        size = doAlign(size);
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

