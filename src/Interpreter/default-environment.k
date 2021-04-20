requires "additional-syntax.k"
requires "Operations/file-operations.k"

module DEFAULT-ENVIRONMENT
    imports ADDITIONAL-SYNTAX
    imports FILE-OPERATIONS

    syntax Map ::= defaultEnvironment()                         [function]
    rule defaultEnvironment() =>
        String2Id("reset") |-> proc(!E , .Ids, env(.Map), reset(!E))
        String2Id("rewrite") |-> proc(!E , .Ids, env(.Map), rewrite(!E))
        String2Id("get") |-> proc(!E , .Ids, env(.Map), get(!E))
        String2Id("put") |-> proc(!E , .Ids, env(.Map), put(!E))
        String2Id("eof") |-> func(!E , .Ids, env(.Map), eof(!E))
endmodule