requires "helper.k"

module SMALL-SYNTAX
    imports ID-SYNTAX
    imports ALTINT-SYNTAX
    imports DOUBLE-SYNTAX
    imports STRING-SYNTAX
    imports INT-SYNTAX
    imports BOOL-SYNTAX

    syntax Pgm ::= "program" Block

    syntax Exp ::= Int
                 | AltInt
                 | Double
                 | Bool
                 | String
                 | Id
                 | "read"
                 | "array" "[" Exp ":" Exp "]"
                 | "record" "(" Ids ")"
                 | "valof" Block
                 | "(" Exp ")"                                  [bracket]
                 > left:
                   Exp "(" Exps ")"
                 > left:
                   Exp "." Exp
                 > Exp "[" Exp "]"
                 > "cont" Exp
                 | "ref" Exp
                 | "!" Exp
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
                 > "jumpout" Id "in" Exp
    syntax Exps ::= List{Exp, ","}

    syntax Com ::= Exp "=" Exp ";"
                 | "output" Exp ";"
                 | Exp "(" Exps ")" ";"
                 | "if" "(" Exp ")" Com "else" Com
                 | "if" "(" Exp ")" Com                         [prefer]
                 | "while" "(" Exp ")" Com
                 | "repeat" Com "until" "(" Exp ")"
                 | "for" "(" Id "=" For ")" Com
                 | "trap" "{" Decs Coms Escs "}"
                 | "escapeto" Id ";"
                 | "return" Exp ";"
                 | "with" Exp "do" Com
                 | Block
    syntax Coms ::= List{Com, ""}
    syntax Esc ::= Id ":" Coms
    syntax Escs ::= List{Esc, ""}

    syntax Dec ::= "const" Id "=" Exp ";"
                 | "var" Id "=" Exp ";"
                 | "array" Id "[" Exp ":" Exp "]" ";"
                 | "record" Id "(" Ids ")" ";"
                 | "file" Id "withbuffer" Id ";"
                 | "proc" Id "(" Ids ")" Block
                 | "rec" "proc" Id "(" Ids ")" Block
                 | "func" Id "(" Ids ")" "{" Exp "}"
                 | "rec" "func" Id "(" Ids ")" "{" Exp "}"
    syntax Decs ::= List{Dec, ""}
    syntax Ids ::= List{Id, ","}

    syntax Block ::= "{" Decs Coms "}"

    syntax For ::= Exp
                 | Exp "while" Exp
                 | Exp "step" Exp "until" Exp
                 | For "," For                                  [left]
endmodule

module ALTINT-SYNTAX
    syntax AltInt ::= r"[+-]?0[xX][0-9a-fA-F]+"                 [prefer, token, prec(2)]
    syntax AltInt ::= r"[+-]?0[oO][0-7]+"                       [prefer, token, prec(2)]
endmodule

module ALTINT
    imports ALTINT-SYNTAX
    imports INT
    imports STRING
    imports HELPER

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

module DOUBLE-SYNTAX
    syntax Double ::= r"[+-]?[0-9]+\\.[0-9]+([eE][+-]?[0-9]+)?" [token, prec(2)]
endmodule

module DOUBLE
    imports DOUBLE-SYNTAX
    imports STRING
    imports FLOAT

    syntax String ::= Double2String(Double)                     [function, functional, hook(STRING.token2string)]

    rule D:Double => String2Float(Double2String(D) +String "d")
endmodule