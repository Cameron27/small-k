requires "../Parser/small-syntax.k"

module INTERPRETER-HELPER
    imports SMALL-SYNTAX

    // Converts a list of ids and type denotations to a list of ids
    syntax Ids ::= IdTypeExps2Ids(IdTypeExps)                 [function]
    rule IdTypeExps2Ids((I : _ , TIs)) => I , IdTypeExps2Ids(TIs)
    rule IdTypeExps2Ids(.IdTypeExps) => .Ids
endmodule