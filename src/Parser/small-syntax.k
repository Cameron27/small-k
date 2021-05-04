requires "double.k"
requires "altint.k"

module SMALL-SYNTAX-BASE
    imports ID-SYNTAX
    imports ALTINT-SYNTAX
    imports DOUBLE-SYNTAX
    imports STRING-SYNTAX
    imports INT-SYNTAX
    imports BOOL-SYNTAX

    syntax Pgm ::= "program" Block

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

    syntax Dec ::= "const" Id ":" TypeDeno "=" Exp ";"
                 | "var" Id ":" TypeDeno "=" Exp ";"
                 | Own
                 | "array" Id "[" Exp ":" Exp "]" ":" TypeDeno ";"
                 | "record" Id "(" IdTypeDenos ")" ";"
                 | "file" Id "withbuffer" Id ":" TypeDeno ";"
                 | "proc" Id "(" IdTypeDenos ")" Block
                 | "rec" "proc" Id "(" IdTypeDenos ")" Block
                 | "func" Id "(" IdTypeDenos ")" ":" TypeDeno "{" Exp "}"
                 | "rec" "func" Id "(" IdTypeDenos ")" ":" TypeDeno "{" Exp "}"
    syntax Own                                                  [locations]
    syntax Own ::= "own" Id ":" TypeDeno "=" Exp ";"
    syntax Decs ::= List{Dec, ""}
    syntax Ids ::= List{Id, ","}

    syntax Block ::= "{" Decs Coms "}"

    syntax Exp ::= Int
                 | AltInt
                 | Double
                 | Bool
                 | String
                 | Id
                 | "read"
                 | "array" "[" Exp ":" Exp "]" ":" TypeDeno
                 | "record" "(" IdTypeDenos ")"
                 | "valof" ":" TypeDeno Block
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
    syntax Exps ::= List{Exp, ","}

    syntax For ::= Exp
                 | Exp "while" Exp
                 | Exp "step" Exp "until" Exp
                 | For "," For                                  [left]

    syntax TypeDeno ::= "int"
                      | "float"
                      | "bool"
                      | "string"
                      | "array" "of" TypeDeno
                      | "record" "(" IdTypeDenos ")"
                      | "proc" "(" TypeDenos ")"
                      | "func" "(" TypeDenos ")" TypeDeno
                      | "file" TypeDeno
                      | "ref" TypeDeno

    syntax TypeDenos ::= List{TypeDeno, ","}
    syntax IdTypeDeno ::= Id ":" TypeDeno
    syntax IdTypeDenos ::= List{IdTypeDeno, ","}
endmodule

module SMALL-SYNTAX
    imports SMALL-SYNTAX-BASE

    syntax Com ::= "trap" Com Escs
                 | "Skip"

    // Simplifications to syntax to reduce number of cases

    // If Then to If Then Else
    rule if ( E ) C => if ( E ) C else Skip                     [anywhere]

    // Array and Record Declarations to Constant Declarations
    rule array I [ E1 : E2 ] : T ; => const I : array of T = array [ E1 : E2 ] : T ;    [anywhere]
    rule record I ( ITs ) ; => const I : record ( ITs ) = record ( ITs ) ;  [anywhere]

    // Remove trap's awkward syntax required to force the correct formatting
    rule trap { Decs Coms Escs } => trap { Decs Coms } Escs     [anywhere]
endmodule