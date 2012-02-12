module mci.core.typing.cache;

import mci.core.common,
       mci.core.container,
       mci.core.nullable,
       mci.core.tuple,
       mci.core.code.functions,
       mci.core.code.modules,
       mci.core.typing.core,
       mci.core.typing.members,
       mci.core.typing.types;

private __gshared NoNullDictionary!(Tuple!(CallingConvention, Type, NoNullList!Type), FunctionPointerType, false) functionPointerTypes;
private __gshared NoNullDictionary!(Type, PointerType, false) pointerTypes;
private __gshared NoNullDictionary!(StructureType, ReferenceType, false) referenceTypes;
private __gshared NoNullDictionary!(Type, ArrayType, false) arrayTypes;
private __gshared NoNullDictionary!(Tuple!(Type, uint), VectorType, false) vectorTypes;

shared static this()
{
    functionPointerTypes = new typeof(functionPointerTypes)();
    pointerTypes = new typeof(pointerTypes)();
    referenceTypes = new typeof(referenceTypes)();
    arrayTypes = new typeof(arrayTypes)();
    vectorTypes = new typeof(vectorTypes)();
}

public FunctionPointerType getFunctionPointerType(CallingConvention callingConvention, Type returnType,
                                                  NoNullList!Type parameterTypes)
in
{
    assert(parameterTypes);
}
out (result)
{
    assert(result);
}
body
{
    synchronized (functionPointerTypes)
    {
        auto params = parameterTypes.duplicate();
        auto tup = tuple(callingConvention, returnType, params);

        if (auto fpType = tup in functionPointerTypes)
            return *fpType;

        return functionPointerTypes[tup] = new FunctionPointerType(callingConvention, returnType, params);
    }
}

public PointerType getPointerType(Type elementType)
in
{
    assert(elementType);
}
out (result)
{
    assert(result);
}
body
{
    synchronized (pointerTypes)
    {
        if (auto ptrType = elementType in pointerTypes)
            return *ptrType;

        return pointerTypes[elementType] = new PointerType(elementType);
    }
}

public ReferenceType getReferenceType(StructureType elementType)
in
{
    assert(elementType);
}
out (result)
{
    assert(result);
}
body
{
    synchronized (referenceTypes)
    {
        if (auto refType = elementType in referenceTypes)
            return *refType;

        return referenceTypes[elementType] = new ReferenceType(elementType);
    }
}

public ArrayType getArrayType(Type elementType)
in
{
    assert(elementType);
}
out (result)
{
    assert(result);
}
body
{
    synchronized (arrayTypes)
    {
        if (auto arrType = elementType in arrayTypes)
            return *arrType;

        return arrayTypes[elementType] = new ArrayType(elementType);
    }
}

public VectorType getVectorType(Type elementType, uint elements)
in
{
    assert(elementType);
}
out (result)
{
    assert(result);
}
body
{
    synchronized (vectorTypes)
    {
        auto tup = tuple(elementType, elements);

        if (auto vecType = tup in vectorTypes)
            return *vecType;

        return vectorTypes[tup] = new VectorType(elementType, elements);
    }
}
