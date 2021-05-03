requires "../Parser/small-syntax.k"

module INTERPRETER-HELPER
    imports SMALL-SYNTAX

    // Converts a list of ids and type denotations to a list of ids
    syntax Ids ::= IdTypeDenos2Ids(IdTypeDenos)                 [function]
    rule IdTypeDenos2Ids((I : _ , TIs)) => I , IdTypeDenos2Ids(TIs)
    rule IdTypeDenos2Ids(.IdTypeDenos) => .Ids
endmodule