module mci.vm.io.common;

public enum string fileMagic = "LAIC"; /// Magic number used for the file format.

public enum uint fileVersion = 40; /// The current version of the file format.

package enum TypeReferenceType : ubyte
{
    core = 0,
    structure = 1,
    pointer = 2,
    reference = 3,
    array = 4,
    vector = 5,
    function_ = 6,
}

package enum CoreTypeIdentifier : ubyte
{
    int8 = 0,
    uint8 = 1,
    int16 = 2,
    uint16 = 3,
    int32 = 4,
    uint32 = 5,
    int64 = 6,
    uint64 = 7,
    int_ = 8,
    uint_ = 9,
    float32 = 10,
    float64 = 11,
}

package enum MetadataType : ubyte
{
    type = 0,
    field = 1,
    function_ = 2,
    parameter = 3,
    register = 4,
    block = 5,
    instruction = 6,
}
