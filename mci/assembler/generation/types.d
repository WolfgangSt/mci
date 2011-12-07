module mci.assembler.generation.types;

import std.conv,
       mci.core.common,
       mci.core.container,
       mci.core.nullable,
       mci.core.code.modules,
       mci.core.typing.core,
       mci.core.typing.cache,
       mci.core.typing.members,
       mci.core.typing.types,
       mci.assembler.parsing.ast,
       mci.assembler.generation.exception,
       mci.assembler.generation.modules;

public StructureType generateType(TypeDeclarationNode node, Module module_)
in
{
    assert(node);
    assert(module_);
}
out (result)
{
    assert(result);
}
body
{
    if (module_.types.get(node.name.name))
        throw new GenerationException("Type " ~ module_.name ~ "/" ~ node.name.name ~ " already defined.", node.location);

    return new StructureType(module_, node.name.name, node.layout);
}

public Field generateField(FieldDeclarationNode node, StructureType type, ModuleManager manager)
in
{
    assert(node);
    assert(type);
    assert(manager);
}
out (result)
{
    assert(result);
}
body
{
    auto fieldType = resolveType(node.type, type.module_, manager);
    auto offset = node.offset ? Nullable!uint(to!uint(node.offset.value)) : Nullable!uint();

    return type.createField(node.name.name, fieldType, node.storage, offset);
}

public Type resolveType(TypeReferenceNode node, Module module_, ModuleManager manager)
in
{
    assert(node);
    assert(module_);
    assert(manager);
}
out (result)
{
    assert(result);
}
body
{
    if (auto structType = cast(StructureTypeReferenceNode)node)
        return resolveStructureType(structType, module_, manager);
    else if (auto fpType = cast(FunctionPointerTypeReferenceNode)node)
        return resolveFunctionPointerType(fpType, module_, manager);
    else if (auto ptrType = cast(PointerTypeReferenceNode)node)
        return getPointerType(resolveType(ptrType.elementType, module_, manager));
    else if (auto arrType = cast(ArrayTypeReferenceNode)node)
        return getArrayType(resolveType(arrType.elementType, module_, manager));
    else if (auto vecType = cast(VectorTypeReferenceNode)node)
    {
        auto elemType = resolveType(vecType.elementType, module_, manager);

        if (!isType!PrimitiveType(elemType))
            throw new GenerationException("Vector elements must be primitive types.", node.location);

        auto elements = to!uint(vecType.elements.value);

        if (!elements)
            throw new GenerationException("Vector types must not have zero elements.", node.location);

        return getVectorType(elemType, elements);
    }
    else
        return getType((cast(CoreTypeReferenceNode)node).name.name);
}

public StructureType resolveStructureType(StructureTypeReferenceNode node, Module module_, ModuleManager manager)
in
{
    assert(node);
    assert(module_);
    assert(manager);
}
out (result)
{
    assert(result);
}
body
{
    // If no module is specified, default to the module the type reference is in.
    auto mod = node.moduleName ? resolveModule(node.moduleName, manager) : module_;

    if (auto type = mod.types.get(node.name.name))
        return *type;

    throw new GenerationException("Unknown type " ~ mod.name ~ "/" ~ node.name.name ~ ".", node.location);
}

public FunctionPointerType resolveFunctionPointerType(FunctionPointerTypeReferenceNode node, Module module_,
                                                      ModuleManager manager)
in
{
    assert(node);
    assert(module_);
    assert(manager);
}
out (result)
{
    assert(result);
}
body
{
    auto returnType = resolveType(node.returnType, module_, manager);
    auto parameterTypes = new NoNullList!Type();

    foreach (paramType; node.parameterTypes)
        parameterTypes.add(resolveType(paramType, module_, manager));

    return getFunctionPointerType(returnType, parameterTypes);
}

public Field resolveField(FieldReferenceNode node, Module module_, ModuleManager manager)
in
{
    assert(node);
    assert(module_);
    assert(manager);
}
out (result)
{
    assert(result);
}
body
{
    auto type = cast(StructureType)resolveType(node.typeName, module_, manager);

    if (auto field = type.fields.get(node.name.name))
        return *field;

    throw new GenerationException("Unknown field " ~ type.module_.name ~ "/" ~ type.name ~ ":" ~ node.name.name ~ ".",
                                  node.location);
}
