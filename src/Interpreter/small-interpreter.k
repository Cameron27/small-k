requires "com.k"
requires "dec.k"
requires "exp.k"
requires "Operations/operations.k"

module SMALL-INTERPRETER
    imports COM
    imports DEC
    imports EXP
    imports OPERATIONS

    // run program
    rule <k> program C => C </k>
         <env> _ => defaultEnvironment() </env>

    // Restore Environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>

    // Handle exitcode
    rule <k> K </k>
         <exit-code> E => 1 </exit-code>
            requires E ==Int 0 andBool K =/=K .                 [priority(1000)]
endmodule