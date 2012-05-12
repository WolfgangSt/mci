module mci.compiler.registers;

import mci.core.nullable;

public abstract class MachineRegister
{
    @property public abstract RegisterCategory category();

    @property public abstract RegisterSize size();

    @property public abstract string name();
}

public enum RegisterCategory : ubyte
{
    general,
    float_,
    vector,
    special,
}

// Note that we set a word to be 32 bits, as opposed to the typical 16 bits.

public enum RegisterSize : ubyte
{
    byte_ = 0x01,
    hword = 0x02,
    word = 0x04,
    dword = 0x08,
    qword = 0x10,
    oword = 0x20,
}

mixin template RegisterBody(string type, string name, RegisterCategory category, ubyte size)
{
    mixin("private __gshared " ~ type ~ " _instance;" ~
          "" ~
          "private this()" ~
          "{" ~
          "}" ~
          "" ~
          "public static " ~ type ~ " opCall()" ~
          "out (result)" ~
          "{" ~
          "    assert(result);" ~
          "}" ~
          "body" ~
          "{" ~
          "    return _instance ? _instance : (_instance = new " ~ type ~ "());" ~
          "}" ~
          "" ~
          "@property public override RegisterCategory category()" ~
          "{" ~
          "    return " ~ category.stringof ~ ";" ~
          "}" ~
          "" ~
          "@property public override RegisterSize size()" ~
          "{" ~
          "    return " ~ (cast(RegisterSize)size).stringof ~ ";" ~
          "}" ~
          "" ~
          "@property public override string name()" ~
          "{" ~
          "    return \"" ~ name ~ "\";" ~
          "}");
}