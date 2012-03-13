module mci.debugger.utilities;

import std.socket,
       mci.core.io,
       mci.core.tuple;

package bool receive(Socket socket, ref ubyte[] buffer, ptrdiff_t expected)
in
{
    assert(socket);
    assert(buffer);
}
body
{
    if (buffer.length < expected)
        buffer.length = expected;

    ptrdiff_t len;

    while (len < expected)
    {
        auto ret = socket.receive(buffer[len .. $ - len]);

        if (!ret || ret == Socket.ERROR)
            return false;

        len += ret;
    }

    return true;
}

package bool send(Socket socket, ubyte[] data)
in
{
    assert(socket);
    assert(data);
}
body
{
    ptrdiff_t len;

    while (len < data.length)
    {
        auto ret = socket.send(data[len .. $ - len]);

        if (ret == Socket.ERROR)
            return false;

        len += ret;
    }

    return true;
}

package Tuple!(ubyte, uint, uint) readHeader(BinaryReader reader)
in
{
    assert(reader);
}
body
{
    auto opCode = reader.read!ubyte();
    auto protoVer = reader.read!uint();
    auto length = reader.read!uint();

    return tuple(opCode, protoVer, length);
}

package void writeHeader(BinaryWriter writer, ubyte opCode, uint protocolVersion, uint length)
in
{
    assert(writer);
}
body
{
    writer.write(opCode);
    writer.write(protocolVersion);
    writer.write(length);
}