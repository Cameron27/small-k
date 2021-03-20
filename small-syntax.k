module SMALL-SYNTAX
    imports ID
    imports MAP
    imports ALTINT
    imports DOUBLE

    syntax Pgm ::= "program" Block

    syntax Exp ::= left:
                 Exp "(" Exp ")"                                [strict]
                 > Int
                 | AltInt
                 | Double
                 | Bool
                 | String
                 | Id
                 | "read"
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
                 > "(" Exp ")"                                  [bracket]


    syntax Com ::= Exp "=" Exp ";"
                 | "output" Exp ";"
                 | Exp "(" Exp ")" ";"                          [strict]
                 | "if" "(" Exp ")" Com "else" Com
                 | "if" "(" Exp ")" Com                         [prefer]
                 | "while" "(" Exp ")" Com
                 | Block
    syntax Coms ::= List{Com, ""}

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

    syntax String ::= dropString(String, Int)                   [function, functional]
    syntax String ::= headString(String)                        [function, functional]

    rule dropString(S, I) => substrString(S, I, lengthString(S))

    rule headString(S) => substrString(S, 0, 1)

    syntax Int ::= charToHex(String)                            [function]

    rule charToHex("0") => 0
    rule charToHex("1") => 1
    rule charToHex("2") => 2
    rule charToHex("3") => 3
    rule charToHex("4") => 4
    rule charToHex("5") => 5
    rule charToHex("6") => 6
    rule charToHex("7") => 7
    rule charToHex("8") => 8
    rule charToHex("9") => 9
    rule charToHex("a") => 10
    rule charToHex("b") => 11
    rule charToHex("c") => 12
    rule charToHex("d") => 13
    rule charToHex("e") => 14
    rule charToHex("f") => 15
    rule charToHex("A") => 10
    rule charToHex("B") => 11
    rule charToHex("C") => 12
    rule charToHex("D") => 13
    rule charToHex("E") => 14
    rule charToHex("F") => 15

    syntax AltInt ::= r"[+-]?0[xX][0-9a-fA-F]+"                 [prefer, token, prec(2)]
    syntax AltInt ::= r"[+-]?0[oO][0-7]+"                       [prefer, token, prec(2)]

    syntax String ::= AltInt2String(AltInt)                     [function, functional, hook(STRING.token2string)]

    syntax AltIntDecode ::= decode(String)
                          | decode(Int, Int, Int, String) // decode(sign, multiplier, current, remaining)

    rule H:AltInt => decode(AltInt2String(H))

    rule decode(S) => decode(#if headString(S) ==String "+" #then 1 #else -1 #fi,
                                #if substrString(S, 2, 3) ==String "x" orBool substrString(S, 2, 3) ==String "X"
                                    #then 16 #else 8 #fi,
                                0, dropString(S, 3))
        requires headString(S) ==String "+" orBool headString(S) ==String "-"
    rule decode(S) => decode("+" +String S)                     [owise]
    rule decode(S, _, C, "") => S *Int C
    rule decode(S, M, C, R)
            => decode(S, M, C *Int M +Int charToHex(headString(R)), dropString(R, 1))   [owise]
endmodule

module DOUBLE
    imports STRING

    syntax Double ::= r"[+-]?[0-9]+\\.[0-9]+([eE][+-]?[0-9]+)?" [token, prec(2)]

    syntax String ::= Double2String(Double)                     [function, functional, hook(STRING.token2string)]

    rule D:Double => String2Float(Double2String(D) +String "d")
endmodule