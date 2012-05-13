module mci.interpreter.debuggee;

import core.sync.condition,
       core.sync.mutex,
       core.time,
       core.thread,
       std.stdio,
       std.socket,
       mci.debugger.server,
       mci.debugger.protocol,
       mci.interpreter.interpreter,
       mci.vm.threading.identity;

/*
void fail()
{
    import mci.core.weak;
    Object w = new Weak!Object(new Object());
}*/

public class InterpreterDebuggerServer: DebuggerServer
{
    private Mutex _waitForConnectionMutex;
    private Mutex _waitForDebuggerMutex;
    private Condition _waitForConnection;
    private Condition _waitForDebugger;
    private bool _isConnected;

    //private core.time.Duration _infinite;

    public this(Interpreter interpreter)
    {
        super(parseAddress("0.0.0.0", 12345));

        _waitForConnectionMutex = new Mutex();
        _waitForDebuggerMutex = new Mutex();

        _waitForConnectionMutex.lock();
        _waitForDebuggerMutex.lock();
        _waitForConnectionMutex.unlock();

        _waitForConnection = new Condition(_waitForConnectionMutex);
        _waitForDebugger = new Condition(_waitForDebuggerMutex);
    }

    protected override void handleConnect(Socket socket)
    {
        _isConnected = true;
        _waitForConnection.notifyAll();
    }

    protected override void handleDisconnect(Socket socket)
    {
        _isConnected = false;
    }

    protected override void handle(Socket client, ClientQueryPacket packet)
    {
    }

    protected override void handle(Socket client, ClientStartPacket packet)
    {
    }

    protected override void handle(Socket client, ClientPausePacket packet)
    {
    }

    protected override void handle(Socket client, ClientContinuePacket packet)
    {
    }

    protected override void handle(Socket client, ClientExitPacket packet)
    {
    }

    protected override void handle(Socket client, ClientThreadPacket packet)
    {
    }

    protected override void handle(Socket client, ClientFramePacket packet)
    {
    }

    protected override void handle(Socket client, ClientBreakpointPacket packet)
    {
    }

    protected override void handle(Socket client, ClientCatchpointPacket packet)
    {
    }

    protected override void handle(Socket client, ClientDisassemblePacket packet)
    {
    }

    protected override void handle(Socket client, ClientInspectPacket packet)
    {
    }

    private void waitForConnection()
    {
        if (!_isConnected)
        {
            writefln("<<Waiting for debugger>>");
            _waitForConnection.wait();
        }
    }

    private void waitAndSend(Packet packet)
    {
        waitForConnection();
        send(packet);
    }



    // called by debuggee threads during execution to wait for continuation
    public void waitForDebugger(InstructionPointer ip)
    {
        auto packet = new ServerBreakPacket();
        packet.thread = getCurrentThreadID();
        packet.moduleName = ip.fun.module_.name;
        packet.functionName = ip.fun.name;
        packet.basicBlockName = ip.block.name;
        packet.instructionIndex = ip.instructionIndex;
        waitAndSend(packet);

        _waitForDebugger.wait();
    }
}
