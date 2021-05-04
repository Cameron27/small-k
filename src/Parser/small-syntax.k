requires "double.k"
requires "altint.k"

// Syntax that is common to the parsed and the extended syntax
module SMALL-SYNTAX-COMMON
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
                 | "escapeto" Id ";"
                 | "return" Exp ";"
                 | "with" Exp "do" Com
                 | Block
    syntax Esc
    syntax Escs ::= List{Esc, ""}
    syntax Block

    syntax Dec ::= "const" Id ":" TypeDeno "=" Exp ";"
                 | "var" Id ":" TypeDeno "=" Exp ";"
                 | Own
                 | "file" Id "withbuffer" Id ":" TypeDeno ";"
                 | "proc" Id "(" IdTypeDenos ")" Block
                 | "rec" "proc" Id "(" IdTypeDenos ")" Block
                 | "func" Id "(" IdTypeDenos ")" ":" TypeDeno "{" Exp "}"
                 | "rec" "func" Id "(" IdTypeDenos ")" ":" TypeDeno "{" Exp "}"
    syntax Own                                                  [locations]
    syntax Own ::= "own" Id ":" TypeDeno "=" Exp ";"
    syntax Ids ::= List{Id, ","}

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

// Syntax additional to the common syntax to complete the parsed syntax
module SMALL-SYNTAX-PARSED
    imports SMALL-SYNTAX-COMMON

    syntax Com ::= "trap" "{" Decs Coms Escs "}"
                 | "for" "(" Id "=" For ")" Com
    syntax Coms ::= List{Com, ""}
    syntax Esc ::= Id ":" Coms
    syntax Block ::= "{" Decs Coms "}"

    syntax For ::= Exp
                 | Exp "while" Exp
                 | Exp "step" Exp "until" Exp
                 | For "," For                                  [left]

    syntax Dec ::= "array" Id "[" Exp ":" Exp "]" ":" TypeDeno ";"
                 | "record" Id "(" IdTypeDenos ")" ";"
    syntax Decs ::= List{Dec, ""}
endmodule

// Syntax additional to the common syntax to complete the extended syntax
module SMALL-SYNTAX
    imports SMALL-SYNTAX-COMMON

    syntax Id ::= "$1" | "$2" | "$3" | "$sign"

    syntax Com ::= "trap" Com Escs
                 | "Skip"
                 | Com ";" Com                                  [right]
    syntax Esc ::= Id "::" Com
    syntax Block ::= "{" Dec ";" Com "}"
                   | "{" Dec "}"
                   | "{" Com "}"
                   | "{" "}"

    syntax Dec ::= "var" Id "=" Exp ";" //TODO: remove this maybe
                 | "SkipDec"
                 | Dec ";" Dec                                  [right]
endmodule

// Applies various conversions to go from the parsed syntax to the extended syntax
module SMALL-SYNTAX-CONVERSION
    imports SMALL-SYNTAX
    imports SMALL-SYNTAX-PARSED
    imports K-EQUAL

    // If Then to If Then Else
    rule if ( E ) C => if ( E ) C else Skip                     [anywhere]

    // Array and Record Declarations to Constant Declarations
    rule array I [ E1 : E2 ] : T ; => const I : array of T = array [ E1 : E2 ] : T ;    [anywhere]
    rule record I ( ITs ) ; => const I : record ( ITs ) = record ( ITs ) ;  [anywhere]

    // Remove trap's awkward syntax required to force the correct formatting
    rule trap { Ds Cs Escs } => trap { Ds Cs } Escs             [anywhere]

    // For
    rule for ( I = E:Exp ) C => I = E ; ; C                     [anywhere]
    rule for ( I = E1 while E2 ) C => {
        var $1 = E1 ; ;
        while (E2) (
            I = $1 ; ;
            C ;
            $1 = E1 ;)
    }                                                           [anywhere]
    rule for ( I = E1 step E2 until E3 ) C => {
        var $1: int = E1 ; ;
        var $2: int = E2 ; ;
        var $3: int = E3 ; ;
        while (($1 - $3) * $sign(cont $2) < 1) (
            I = $1 ; ;
            C ;
            $1 = $1 + $2 ; ;
            $2 = E2 ; ;
            $3 = E3 ;
        )
    }                                                           [anywhere]
    rule for ( I = F1 , F2 ) C =>
        (for ( I = F1 ) C) ;
        (for ( I = F2 ) C)                                      [anywhere]

    // Convert syntax that uses Coms or Decs to a version that does not
    rule { Ds:Decs Cs:Coms } => { convert(Ds) ; convert(Cs) }   [anywhere]
    rule I : C:Coms => I :: convert(C)                          [anywhere]

    // Convert uses of Coms and Decs to chains
    syntax Com ::= convert(Coms)                                [function]
    syntax Dec ::= convert(Decs)                                [function]
    rule convert(C:Com Cs) => C ; convert(Cs)
    rule convert(.Coms) => Skip
    rule convert(D:Dec Ds) => D ; convert(Ds)
    rule convert(.Decs) => SkipDec
endmodule