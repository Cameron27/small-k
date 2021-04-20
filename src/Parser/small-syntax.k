requires "double.k"
requires "altint.k"

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
                 | Own
                 | "array" Id "[" Exp ":" Exp "]" ";"
                 | "record" Id "(" Ids ")" ";"
                 | "file" Id "withbuffer" Id ";"
                 | "proc" Id "(" Ids ")" Block
                 | "rec" "proc" Id "(" Ids ")" Block
                 | "func" Id "(" Ids ")" "{" Exp "}"
                 | "rec" "func" Id "(" Ids ")" "{" Exp "}"
    syntax Own                                                  [locations]
    syntax Own ::= "own" Id "=" Exp ";"
    syntax Decs ::= List{Dec, ""}
    syntax Ids ::= List{Id, ","}

    syntax Block ::= "{" Decs Coms "}"

    syntax For ::= Exp
                 | Exp "while" Exp
                 | Exp "step" Exp "until" Exp
                 | For "," For                                  [left]
endmodule
