requires "double.k"
requires "altint.k"

// Syntax that is common to the parsed and the extended syntax
module SMALL-SYNTAX-COMMON
    imports ID-SYNTAX
    imports STRING-SYNTAX
    imports UNSIGNED-INT-SYNTAX
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

    syntax Exp ::= Bool
                 | String
                 | Id
                 | "read"
                 | "this"
                 | Null
                 | "array" "[" Exp ":" Exp "]" ":" TypeDeno
                 | "record" "(" IdTypeDenos ")"
                 | "valof" ":" TypeDeno Block
                 | "(" Exp ")"                                  [bracket]
                 > left:
                   Exp "(" Exps ")"
                 | Exp "." Exp
                 | Exp "[" Exp "]"
                 > "cont" Exp
                 | "ref" Exp
                 | "!" Exp
                 | "+" Exp
                 | "-" Exp
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

    syntax Null ::= "null"

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
                      | Id

    syntax TypeDenos ::= List{TypeDeno, ","}
    syntax IdTypeDeno ::= Id ":" TypeDeno
    syntax IdTypeDenos ::= List{IdTypeDeno, ","}
endmodule

// Syntax additional to the common syntax to complete the parsed syntax
module SMALL-SYNTAX-PARSED
    imports SMALL-SYNTAX-COMMON
    imports ALTINT-SYNTAX
    imports DOUBLE-SYNTAX

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
                 | "class" Id "{" SCDecs "}"
    syntax Decs ::= List{Dec, ""}

    syntax SCDec ::= "public" CDec
                   | "private" CDec
                   | CDec
    syntax SCDecs ::= List{SCDec, ""}

    syntax CDec ::= "const" Id ":" TypeDeno "=" Exp ";"
                  | "var" Id ":" TypeDeno "=" Exp ";"
                  | "file" Id "withbuffer" Id ":" TypeDeno ";"
                  | "proc" Id "(" IdTypeDenos ")" Block
                  | "func" Id "(" IdTypeDenos ")" ":" TypeDeno "{" Exp "}"
                  | "array" Id "[" Exp ":" Exp "]" ":" TypeDeno ";"
                  | "record" Id "(" IdTypeDenos ")" ";"

    syntax Exp ::= Int
                 | AltInt
                 | Double
                 | "new" Id "(" ")"
endmodule

// Syntax additional to the common syntax to complete the extended syntax
module SMALL-SYNTAX
    imports SMALL-SYNTAX-COMMON
    imports FLOAT-SYNTAX
    imports MINT-SYNTAX

    syntax Id ::= "$1" | "$2" | "$3" | "$sign"

    syntax Com ::= "trap" Com Escs
                 | "Skip"
                 | Com ";" Com                                  [right]
    syntax Esc ::= Id "::" Com
    syntax Block ::= "{" Dec ";" Com "}"
                   | "{" Dec "}"
                   | "{" Com "}"
                   | "{" "}"

    syntax Dec ::= "class" Id SCDec
                 | "SkipDec"
                 | Dec ";" Dec                                  [right]

    syntax SCDec ::= "public" Dec
                   | "private" Dec
                   | "SkipSCDec"
                   | SCDec ";" SCDec                            [right]

    syntax Exp ::= MInt{64}
                 | Float
                 | "new" Exp
    syntax MInt{64}

    syntax TypeDeno ::= typeInfer(Exp)
endmodule

// Applies various conversions to go from the parsed syntax to the extended syntax
module SMALL-SYNTAX-CONVERSION
    imports SMALL-SYNTAX
    imports SMALL-SYNTAX-PARSED
    imports K-EQUAL
    imports ALTINT
    imports DOUBLE
    imports MINT

    // If Then to If Then Else
    rule if ( E ) C => if ( E ) C else Skip                     [anywhere]

    // Array and Record Declarations to Constant Declarations
    rule (array I [ E1 : E2 ] : T ;):Dec => const I : array of T = array [ E1 : E2 ] : T ;  [anywhere]
    rule (record I ( ITs ) ;):Dec => const I : record ( ITs ) = record ( ITs ) ;    [anywhere]

    // Remove trap's awkward syntax required to force the correct formatting
    rule trap { Ds Cs Escs } => trap { Ds Cs } Escs             [anywhere]

    // Convert for loops to other forms
    rule for ( I = E:Exp ) C => I = E ; ; C                     [anywhere]
    rule for ( I = E1 while E2 ) C => {
        var $1: typeInfer(E1) = E1 ; ;
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

    // Covert CDecs in class to Decs
    rule class I { SCDs } => class I convertSCDecs(SCDs)        [anywhere]

    // Convert Id in new to an Exp
    rule new I ( ) => new I

    // Convert syntax that uses Coms or Decs to a version that does not
    rule { Ds:Decs Cs:Coms } => { convertDecs(Ds) ; convertComs(Cs) }   [anywhere]
    rule I : C:Coms => I :: convertComs(C)                      [anywhere]

    // Convert uses of Coms to chains
    syntax Com ::= convertComs(Coms)                            [function]
    rule convertComs(C Cs) => C ; convertComs(Cs)
    rule convertComs(.Coms) => Skip

    // Convert uses of Decs to chains
    syntax Dec ::= convertDecs(Decs)                            [function]
    rule convertDecs(D Ds) => D ; convertDecs(Ds)
    rule convertDecs(.Decs) => SkipDec

    // Convert uses of SCDecs to chains
    syntax SCDec ::= convertSCDecs(SCDecs)                      [function]
    rule convertSCDecs(SCD SCDs) => convertSCDec(SCD) ; convertSCDecs(SCDs)
    rule convertSCDecs(.SCDecs) => SkipSCDec

    // Convert SCDec to from CDec versions to Dec versions
    syntax SCDec ::= convertSCDec(SCDec)                        [function]
    rule convertSCDec(public CD) => public convertCDec(CD)
    rule convertSCDec(private CD) => private convertCDec(CD)
    rule convertSCDec(CD) => private convertCDec(CD)

    // Convert CDec to Dec
    syntax Dec ::= convertCDec(CDec)                            [function]
    rule convertCDec(const I : T = E ;) => const I : T = E ;
    rule convertCDec(var I : T = E ;) => var I : T = E ;
    rule convertCDec(file I1 withbuffer I2 : T ;) => file I1 withbuffer I2 : T ;
    rule convertCDec(proc I ( ITs ) C) => proc I ( ITs ) C
    rule convertCDec(func I ( ITs ) : T { E }) => func I ( ITs ) : T { E }
    rule convertCDec(array I [ E1 : E2 ] : T ;) => array I [ E1 : E2 ] : T ;
    rule convertCDec(record I ( ITs ) ;) => record I ( ITs ) ;

    // Convert alt-ints to ints
    rule AI:AltInt => AltInt2Int(AI)

    // Convert doubles to floats
    rule D:Double => Double2Float(D)

    // Convert ints to int32s
    rule I:Int => Int2MInt(I)::MInt{64}
endmodule