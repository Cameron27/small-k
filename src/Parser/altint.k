requires "../Common/helper.k"

module ALTINT-SYNTAX
    syntax AltInt ::= r"0[xX][0-9a-fA-F]+"                      [prefer, token, prec(2)]
    syntax AltInt ::= r"0[oO][0-7]+"                            [prefer, token, prec(2)]
endmodule

module ALTINT
    imports ALTINT-SYNTAX
    imports INT
    imports STRING
    imports HELPER

    syntax Int ::= AltInt2Int(AltInt)                           [function, functional]
    rule AltInt2Int(AI) => decode(AltInt2String(AI))

    syntax String ::= AltInt2String(AltInt)                     [function, functional, hook(STRING.token2string)]

    syntax Int ::= decode(String)                               [function]
                 | decode(Int, String) /* decode(sign, base, value) */  [function]

    rule decode(S) => decode(#if substrString(S, 1, 2) ==String "x" orBool substrString(S, 1, 2) ==String "X"
                                    #then 16 #else 8 #fi,
                                dropString(S, 2))
    rule decode(B, V) => String2Base(V, B)
endmodule
