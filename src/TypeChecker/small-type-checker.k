requires "com.k"
requires "dec.k"
requires "exp.k"
requires "operations.k"
requires "type-deno.k"
requires "default-environment.k"

module SMALL-TYPE-CHECKER
    imports COM
    imports DEC
    imports EXP
    imports OPERATIONS
    imports TYPE-DENO
    imports DEFAULT-ENVIRONMENT
    imports BOOL
    imports INT

    // run program
    rule <k> program C => C </k>
         <tenv> _ => defaultEnvironment() </tenv>

    // Handle exitcode
    rule <k> K </k>
         <exit-code> E => 2 </exit-code>
            requires E ==Int 0 andBool K =/=K .                 [priority(1000)]
endmodule