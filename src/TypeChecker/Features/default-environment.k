requires "../Core/type.k"

module DEFAULT-ENVIRONMENT
    imports TYPE
    imports ID

    syntax Map ::= defaultEnvironment()                         [function]
    rule defaultEnvironment() =>
        String2Id("reset") |-> TProc TRef TFileAny
        String2Id("rewrite") |-> TProc TRef TFileAny
        String2Id("get") |-> TProc TRef TFileAny
        String2Id("put") |-> TProc TRef TFileAny
        String2Id("eof") |-> TFunc TRef TFileAny TBool
endmodule