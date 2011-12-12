module mci.interpreter.exception;

import mci.core.exception,
	mci.core.diagnostics.debugging;

public class InterpreterException : CompilerException
{
    public this(string msg, string file = __FILE__, size_t line = __LINE__)
    in
    {
        assert(msg);
        assert(file);
        assert(line);
    }
    body
    {
        super(msg, file, line);
    }

    public this(string msg, Throwable next, string file = __FILE__,
                size_t line = __LINE__)
    in
    {
        assert(msg);
        assert(next);
        assert(file);
        assert(line);
    }
    body
    {
        super(msg, next, file, line);
    }
}