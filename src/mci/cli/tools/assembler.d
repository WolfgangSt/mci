module mci.cli.tools.assembler;

import std.getopt,
       std.path,
       std.stdio,
       std.utf,
       mci.assembler.disassembly.ast,
       mci.assembler.exception,
       mci.assembler.generation.driver,
       mci.assembler.generation.exception,
       mci.assembler.parsing.exception,
       mci.assembler.parsing.lexer,
       mci.assembler.parsing.parser,
       mci.core.common,
       mci.core.config,
       mci.core.container,
       mci.core.exception,
       mci.core.io,
       mci.core.code.functions,
       mci.core.code.modules,
       mci.vm.exception,
       mci.vm.execution,
       mci.vm.intrinsics.declarations,
       mci.vm.io.writer,
       mci.vm.memory.prettyprint,
       mci.vm.trace,
       mci.cli.main,
       mci.cli.tool,
       mci.cli.tools.interpreter,
       mci.interpreter.interpreter,
       mci.vm.memory.base,
       mci.vm.memory.dgc,
       mci.vm.memory.libc;

static if (operatingSystem != OperatingSystem.windows)
{
    import mci.vm.memory.boehm;
}

public enum string inputFileExtension = ".ial";

public final class AssemblerTool : Tool
{
    @property public string name() pure nothrow
    {
        return "asm";
    }

    @property public string description() pure nothrow
    {
        return "Assemble IAL files into a module.";
    }

    @property public string[] options() pure nothrow
    {
        return ["\t--output=<file>\t\t-o <file>\tSpecify module output file.",
                "\t--dump=<file>\t\t-d <file>\tDump parsed ASTs to the given file.",
                "\t--interpret\t\t-i\t\tRun the module with the IAL interpreter (no output will be generated).",
                "\t--collector=<type>\t-c <type>\tSpecify which garbage collector to use if running the module."];
    }

    public int run(string[] args)
    {
        string output = "out.mci";
        string dump;
        bool interpret;
        GarbageCollectorType gcType;

        try
        {
            getopt(args,
                   config.caseSensitive,
                   config.bundling,
                   "output|o", &output,
                   "dump|d", &dump,
                   "interpret|i", &interpret,
                   "collector|c", &gcType);
            args = args[1 .. $];
        }
        catch (Exception ex)
        {
            logf("Error: Could not parse command line: %s", ex.msg);
            return 2;
        }

        if (args.length == 0)
        {
            log("Error: No files given.");
            return 2;
        }

        if (output[0] == '.' && output.length <= moduleFileExtension.length + 1)
        {
            logf("Error: Output file '%s' has no name part.", output);
            return 2;
        }

        if (extension(output) != moduleFileExtension)
        {
            logf("Error: Output file '%s' does not end in '%s'.", output, moduleFileExtension);
            return 2;
        }

        string[] files;

        foreach (file; args)
        {
            if (file[0] == '.' && file.length <= moduleFileExtension.length + 1)
            {
                logf("Error: File '%s' has no name part.", file);
                return 2;
            }

            if (extension(file) != inputFileExtension)
            {
                logf("Error: File '%s' does not end in '%s'.", file, inputFileExtension);
                return 2;
            }

            foreach (f; files)
            {
                if (file == f)
                {
                    logf("Error: File '%s' specified multiple times.", file);
                    return 2;
                }
            }

            files ~= file;
        }

        auto units = new NoNullDictionary!(string, CompilationUnit)();

        foreach (file; args)
        {
            FileStream stream;

            try
            {
                stream = new FileStream(file, FileMode.read);
                auto source = new Source((new BinaryReader(stream)).readArray!string(stream.length));
                auto lexer = new Lexer(source);
                auto parser = new Parser(lexer.lex());
                auto unit = parser.parse();

                units.add(file, unit);
            }
            catch (IOException ex)
            {
                logf("Error: Could not access '%s': %s", file, ex.msg);
                return 1;
            }
            catch (UTFException ex)
            {
                logf("Error: UTF-8 decoding failed; file '%s' is probably not plain text.", file);
                return 1;
            }
            catch (LexerException ex)
            {
                logf("Error: Lexing failed in '%s' %s: %s", file, ex.location, ex.msg);
                return 1;
            }
            catch (ParserException ex)
            {
                logf("Error: Parsing failed in '%s' %s: %s", file, ex.location, ex.msg);
                return 1;
            }
            finally
            {
                if (stream)
                    stream.close();
            }
        }

        if (dump)
        {
            FileStream dumpStream;

            try
            {
                dumpStream = new FileStream(dump, FileMode.truncate);

                foreach (unit; units)
                {
                    auto disasm = new TreeDisassembler(dumpStream);
                    disasm.disassemble(unit.x, unit.y);
                }
            }
            catch (IOException ex)
            {
                logf("Error: Could not access '%s': %s", dump, ex.msg);
                return 1;
            }
            finally
            {
                if (dumpStream)
                    dumpStream.close();
            }
        }

        GeneratorDriver driver;

        try
        {
            auto manager = new ModuleManager();
            manager.attach(intrinsicModule);

            driver = new GeneratorDriver(baseName(output[0 .. $ - moduleFileExtension.length]), manager, units);
            auto mod = driver.run();

            auto writer = new ModuleWriter();
            if (interpret)
            {
                GarbageCollector gc;
                final switch (gcType)
                {
                    case GarbageCollectorType.libc:
                        gc = new LibCGarbageCollector();
                        break;
                    case GarbageCollectorType.dgc:
                        gc = new DGarbageCollector();
                        break;
                    static if (operatingSystem != OperatingSystem.windows)
                    {
                        case GarbageCollectorType.boehm:
                            gc = new BoehmGarbageCollector();
                            break;
                    }
                }
                ExecutionEngine interpreter = new Interpreter(gc);
                auto main = mod.functions["main"];
                auto params = new NoNullList!RuntimeValue();

                try
                {
                    auto result = interpreter.execute(main, params);

                    if (result !is null)
                    {
                        logf("The program quitted with:");
                        logf( prettyPrint( result.type, mci.core.config.is32Bit, result.data, "(return value)" ) );
                    }
                    else
                        logf("The program quitted without return value.");
                }
                catch (ExecutionException ex)
                {
                    auto faultPoint = ex.trace.frames[0].instruction;
                    auto faultBlock = faultPoint.block;
                    auto instructionIndex = findIndex(faultBlock.stream, faultPoint);
                    logf("Unhandled exception thrown at %s.%s.%s: %s", faultBlock.function_.name, faultBlock.name, instructionIndex, faultPoint.toString());
                    logf("==========  Exception  ==========");
                    logf(prettyPrint(ex.exception.type, mci.core.config.is32Bit, cast(ubyte*)ex.exception.data, "exception"));
                    logf("========== Stack Trace ==========");
                    foreach (StackFrame frame; ex.trace.frames)
                    {
                        auto inst = frame.instruction;
                        auto block = inst.block;
                        auto index = findIndex(block.stream, inst);
                        logf("%s.%s.%s: %s", block.function_.name, block.name, index, inst.toString());
                    }
                    logf("=================================");
                }

                return true;
            }
            (new ModuleWriter()).save(mod, output);
        }
        catch (IOException ex)
        {
            logf("Error: Could not access '%s': %s", output, ex.msg);
            return 1;
        }
        catch (GenerationException ex)
        {
            logf("Error: Generation failed in '%s' %s: %s", driver.currentFile, ex.location, ex.msg);
            return 1;
        }

        return 0;
    }
}
