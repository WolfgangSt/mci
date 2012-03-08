module mci.vm.memory.prettyprint;

import std.ascii,
       std.conv,
       std.string,
       mci.core.common,
       mci.core.container,
       mci.core.typing.core,
       mci.core.typing.members,
       mci.core.typing.types,
       mci.vm.memory.base,
       mci.vm.memory.layout;


private final class LineInfo
{
    public LineInfo next;
    public string line;
    public size_t indent;
    public List!(ubyte*) xrefs; // OPTLINK ERROR: shall be LineInfo
    public string arrowPrefix;

    public void appendArrow(string s, size_t depth)
    {
        auto len = arrowPrefix.length;
        while (len++ < depth)
            arrowPrefix ~= " ";
        arrowPrefix ~= s;
    }

    public void addXref(LineInfo li)
    {
        if (!xrefs)
            xrefs = new List!(ubyte*);
        xrefs.add(HACK_TO_PTR(li));
    }

    public string format()
    {
        auto s = arrowPrefix;
        for (auto i = 0; i < indent; i++)
            s ~= "    ";
        s ~= line;

        return s;
    }
}

private ubyte* HACK_TO_PTR(LineInfo li) // OPTLINK FAULT WORKAROUND
{
    return cast(ubyte*)li;
}

private ubyte* HACK_TO_PTR(RuntimeObject* rto) // OPTLINK FAULT WORKAROUND
{
    return cast(ubyte*)rto;
}

private LineInfo* HACK_TO_LINEP(ubyte** p) // OPTLINK FAULT WORKAROUND
{
    return cast(LineInfo*)p;
}

private LineInfo HACK_TO_LINE(ubyte* p) // OPTLINK FAULT WORKAROUND
{
    return cast(LineInfo)p;
}

private final class PrettyPrinter
{
    private size_t _indent;
    private Dictionary!(ubyte*, ubyte*) _rtoLines; // OPTLINK ERROR: shall be RuntimeObject, LineInfo
    private LineInfo _firstLine;
    private LineInfo _currentLine;

    public this()
    {
        _rtoLines = new Dictionary!(ubyte*, ubyte*)();
    }

    private void newLine()
    {
        auto line = new LineInfo();

        if (_currentLine)
        {
            _currentLine.next = line;
            _currentLine = line;
        } else
        {
            _currentLine = line;
            _firstLine = line;
        }
    }

    private void flush(string line)
    {
        _currentLine.indent = _indent;
        _currentLine.line = line;
    }

    private void processStruct(StructureType struc, ubyte* mem, bool is32Bit)
    {
        newLine();
        flush("{");
        _indent++;

        foreach (field; struc.fields)
        {
            auto offset = computeOffset(field.y, is32Bit);
            processField(field.y.type, mem + offset, is32Bit, field.x);
        }

        _indent--;
        newLine();
        flush("}");
    }

    private void processField(Type type, ubyte* mem, bool is32Bit, string instanceName)
    in
    {
        assert(type);
        assert(mem);
    }
    body
    {
        newLine();
        auto s = (format("[%s] ", type.name));

        if (instanceName)
            s ~= (instanceName ~ ": ");

        void arrayOrVector(Type type)
        in
        {
            assert(cast(ArrayType)type || cast(VectorType)type);
        }
        body
        {
            auto vec = cast(VectorType)type;
            auto arr = cast(ArrayType)type;

            auto rto = *cast(RuntimeObject**)mem;
            flush(s ~ format("0x%x", cast(ubyte*)rto));

            if (!rto)
                return;

            if (auto line = HACK_TO_LINEP(_rtoLines.get(HACK_TO_PTR(rto))))
                return line.addXref(_currentLine);

            _rtoLines.add(HACK_TO_PTR(rto), HACK_TO_PTR(_currentLine));

            auto p = rto.data;

            auto elementCount = arr ? *cast(size_t*)p : vec.elements;
            auto elementType = arr ? arr.elementType : vec.elementType;
            auto elementSize = computeSize(elementType, is32Bit);

            if (arr)
                p += computeSize(NativeUIntType.instance, is32Bit);

            newLine();
            flush("{");
            _indent++;

            for (size_t i = 0; i < elementCount; i++)
            {
                processField(elementType, p, is32Bit, to!string(i));
                p += elementSize;
            }

            _indent--;
            newLine();
            flush("}");
        }

        return match(type,
                     (Int8Type t) => flush(s ~ format("%s", *cast(byte*)mem)),
                     (UInt8Type t) => flush(s ~ format("%s", *cast(ubyte*)mem)),
                     (Int16Type t) => flush(s ~ format("%s", *cast(short*)mem)),
                     (UInt16Type t) => flush(s ~ format("%s", *cast(ushort*)mem)),
                     (Int32Type t) => flush(s ~ format("%s", *cast(int*)mem)),
                     (UInt32Type t) => flush(s ~ format("%s", *cast(uint*)mem)),
                     (Int64Type t) => flush(s ~ format("%s", *cast(long*)mem)),
                     (UInt64Type t) => flush(s ~ format("%s", *cast(ulong*)mem)),
                     (NativeIntType t) => flush(s ~ format("%s", *cast(isize_t*)mem)),
                     (NativeUIntType t) => flush(s ~ format("%s", *cast(size_t*)mem)),
                     (Float32Type t) => flush(s ~ format("%s", *cast(float*)mem)),
                     (Float64Type t) => flush(s ~ format("%s", *cast(double*)mem)),
                     (StructureType t)
                     {
                         flush(s);
                         processStruct(t, mem, is32Bit);
                     },
                     (ReferenceType t)
                     {
                         auto rto = *cast(RuntimeObject**)mem;
                         flush(s ~ format("0x%x", cast(ubyte*)rto));

                         if (!rto)
                             return;

                         if (auto line = HACK_TO_LINEP(_rtoLines.get(HACK_TO_PTR(rto))))
                             return line.addXref(_currentLine);

                         _rtoLines.add(HACK_TO_PTR(rto), HACK_TO_PTR(_currentLine));
                         processStruct(t.elementType, rto.data, is32Bit);
                     },
                     (VectorType t) => arrayOrVector(t),
                     (ArrayType t) => arrayOrVector(t),
                     () => flush(s ~ format("0x%x", *cast(size_t*)mem)));
    }

    private void addArrows()
    {
        size_t maxDepth = 0;
        for (auto line = _firstLine; line; line = line.next)
        {
            if (!line.xrefs)
                continue;

            auto end = HACK_TO_LINE(line.xrefs[line.xrefs.count - 1]);
            auto depth = line.arrowPrefix.length;
            if (depth + 1 > maxDepth)
                maxDepth = depth + 1;
            size_t nextRefIdx = 0;
            auto nextRef = HACK_TO_LINE(line.xrefs[nextRefIdx++]);
            for (auto x = line; x !is end; x = x.next)
            {
                if (x is line)
                    x.appendArrow(">", depth);
                else if (x is nextRef)
                {
                    x.appendArrow("*", depth);
                    nextRef = HACK_TO_LINE(line.xrefs[nextRefIdx++]);
                }
                else
                    x.appendArrow("|", depth);
            }
            end.appendArrow("*", depth);
        }

        for (auto line = _firstLine; line; line = line.next)
            line.appendArrow("", maxDepth);
    }

    public string process(Type type, ubyte* mem, bool is32Bit, string instanceName, bool drawReferences)
    {
        processField(type, mem, is32Bit, instanceName);

        if (drawReferences)
            addArrows();

        string s;
        for (auto line = _firstLine; line; line = line.next)
            s ~= line.format() ~ std.ascii.newline;

        return s;
    }
}

public string prettyPrint(Type type, bool is32Bit, ubyte* mem, string instanceName, bool drawReferences = true)
in
{
    assert(type);
    assert(mem);
}
out (result)
{
    assert(result);
}
body
{
    return (new PrettyPrinter()).process(type, mem, is32Bit, instanceName, drawReferences);
}
