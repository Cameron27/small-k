requires "Core/com.k"
requires "Core/dec.k"
requires "Core/exp.k"
requires "Core/type-deno.k"
requires "Features/operations.k"
requires "Features/default-environment.k"
requires "Features/classes.k"
requires "Features/files.k"
requires "../Parser/small-syntax.k"

module SMALL-TYPE-CHECKER
    imports COM
    imports DEC
    imports EXP
    imports OPERATIONS
    imports TYPE-DENO
    imports DEFAULT-ENVIRONMENT
    imports BOOL
    imports INT
    imports SMALL-SYNTAX-CONVERSION
    imports CLASSES
    imports FILES

    // run program
    rule <k> program C => C </k>
         <tenv> _ => defaultEnvironment() </tenv>
         <classes> _ => -1 |-> TClass -1 .Map </classes>

    // Handle exitcode
    rule <k> K </k>
         <exit-code> 0 => 2 </exit-code>
            requires K =/=K .                                   [priority(1000)]
endmodule