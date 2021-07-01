requires "Core/com.k"
requires "Core/dec.k"
requires "Core/exp.k"
requires "Features/classes.k"
requires "Features/operations.k"
requires "Features/files.k"
requires "Features/for.k"
requires "../Parser/small-syntax.k"

module SMALL-INTERPRETER
    imports COM
    imports DEC
    imports EXP
    imports CLASSES
    imports OPERATIONS
    imports FILES
    imports FOR
    imports SMALL-SYNTAX-CONVERSION

    // run program
    rule <k> program C => C </k>
         <env> _ => defaultEnvironment() </env>

    // Handle exitcode
    rule <k> K </k>
         <exit-code> 0 => 1 </exit-code>
            requires K =/=K .                                   [priority(1000)]
endmodule