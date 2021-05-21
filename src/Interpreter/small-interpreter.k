requires "Core/com.k"
requires "Core/dec.k"
requires "Core/exp.k"
requires "Features/classes.k"
requires "Features/operations.k"
requires "Features/files.k"
requires "../Parser/small-syntax.k"

module SMALL-INTERPRETER
    imports COM
    imports DEC
    imports EXP
    imports CLASSES
    imports OPERATIONS
    imports FILES
    imports SMALL-SYNTAX-CONVERSION

    // run program
    rule <k> program C => C </k>
         <env> _ => defaultEnvironment() </env>

    // Handle exitcode
    rule <k> K </k>
         <exit-code> E => 1 </exit-code>
            requires E ==Int 0 andBool K =/=K .                 [priority(1000)]
endmodule