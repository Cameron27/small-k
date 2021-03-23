requires "helper.k"

module SMALL-SYNTAX
    imports ID
    imports MAP
    imports ALTINT
    imports DOUBLE

    syntax Pgm ::= "program" Block

    syntax Exp ::= Int
                 | AltInt
                 | Double
                 | Bool
                 | String
                 | Id
                 | "read"
                 | "(" Exp ")"                                  [bracket]
                 > left:
                   Exp "(" Exp ")"                              [strict]
                 > left:
                   Exp "*" Exp
                 | Exp "/" Exp
                 | Exp "%" Exp
                 > left:
                   Exp "+" Exp
                 | Exp "-" Exp
                 > left:
                   Exp "<" Exp
                 | Exp "<=" Exp
                 | Exp ">" Exp
                 | Exp ">=" Exp
                 > left:
                   Exp "==" Exp
                 | Exp "!=" Exp
                 > left:
                   Exp "&" Exp
                 > left:
                   Exp "^" Exp
                 > left:
                   Exp "|" Exp
                 > right:
                   Exp "?" Exp ":" Exp


    syntax Com ::= Exp "=" Exp ";"
                 | "output" Exp ";"
                 | Exp "(" Exp ")" ";"                          [strict]
                 | "if" "(" Exp ")" Com "else" Com
                 | "if" "(" Exp ")" Com                         [prefer]
                 | "while" "(" Exp ")" Com
                 | "trap" "{" Decs Coms Escs "}"
                 | "escapeto" Id ";"
                 | Block
    syntax Coms ::= List{Com, ""}
    syntax Esc ::= Id ":" Coms
    syntax Escs ::= List{Esc, ""}

    syntax Dec ::= "const" Id "=" Exp ";"
                 | "var" Id "=" Exp ";"
                 | "proc" Id "(" Id ")" Block
                 | "func" Id "(" Id ")" "{" Exp "}"
    syntax Decs ::= List{Dec, ""}

    syntax Block ::= "{" Decs Coms "}"
endmodule

module ALTINT
    imports INT
    imports STRING
    imports HELPER

    syntax AltInt ::= r"[+-]?0[xX][0-9a-fA-F]+"                 [prefer, token, prec(2)]
    syntax AltInt ::= r"[+-]?0[oO][0-7]+"                       [prefer, token, prec(2)]

    syntax String ::= AltInt2String(AltInt)                     [function, functional, hook(STRING.token2string)]

    syntax AltIntDecode ::= decode(String)
                          | decode(Int, Int, String) // decode(sign, base, value)

    rule H:AltInt => decode(AltInt2String(H))

    rule decode(S) => decode(#if headString(S) ==String "+" #then 1 #else -1 #fi,
                                #if substrString(S, 2, 3) ==String "x" orBool substrString(S, 2, 3) ==String "X"
                                    #then 16 #else 8 #fi,
                                dropString(S, 3))
        requires headString(S) ==String "+" orBool headString(S) ==String "-"
    rule decode(S) => decode("+" +String S)                     [owise]
    rule decode(S, B, V) => S *Int String2Base(V, B)
endmodule

module DOUBLE
    imports STRING
    imports FLOAT

    syntax Double ::= r"[+-]?[0-9]+\\.[0-9]+([eE][+-]?[0-9]+)?" [token, prec(2)]

    syntax String ::= Double2String(Double)                     [function, functional, hook(STRING.token2string)]

    rule D:Double => String2Float(Double2String(D) +String "d")
endmodule