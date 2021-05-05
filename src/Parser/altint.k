requires "../Common/helper.k"

module ALTINT-SYNTAX
    syntax AltInt ::= r"[+-]?0[xX][0-9a-fA-F]+"                 [prefer, token, prec(2)]
    syntax AltInt ::= r"[+-]?0[oO][0-7]+"                       [prefer, token, prec(2)]
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
                 | decode(Int, Int, String) /* decode(sign, base, value) */ [function]

    rule decode(S) => decode(#if headString(S) ==String "+" #then 1 #else -1 #fi,
                                #if substrString(S, 2, 3) ==String "x" orBool substrString(S, 2, 3) ==String "X"
                                    #then 16 #else 8 #fi,
                                dropString(S, 3))
        requires headString(S) ==String "+" orBool headString(S) ==String "-"
    rule decode(S) => decode("+" +String S)                     [owise]
    rule decode(S, B, V) => S *Int String2Base(V, B)
endmodule
