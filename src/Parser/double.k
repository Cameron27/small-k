module DOUBLE-SYNTAX
    syntax Double ::= r"[+-]?[0-9]+\\.[0-9]+([eE][+-]?[0-9]+)?" [token, prec(2)]
endmodule

module DOUBLE
    imports DOUBLE-SYNTAX
    imports STRING
    imports FLOAT

    syntax Float ::= Double2Float(Double)                       [function, functional]

    rule Double2Float(D) => String2Float(Double2String(D) +String "d")

    syntax String ::= Double2String(Double)                     [function, functional, hook(STRING.token2string)]
endmodule