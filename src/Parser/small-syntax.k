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
                 | Acc "(" Exps ")" ";"
                 | "if" "(" Exp ")" Com "else" Com
                 | "if" "(" Exp ")" Com                         [prefer]
                 | "while" "(" Exp ")" Com
                 | "repeat" Com "until" "(" Exp ")"
                 | "for" "(" Id "=" For ")" Com
                 | "escapeto" Id ";"
                 | "return" Exp ";"
                 | "with" Exp "do" Com
                 | Block
    syntax Esc
    syntax Escs ::= List{Esc, ""}
    syntax Block

    syntax For ::= Exp
                 | Exp "while" Exp
                 | Exp "step" Exp "until" Exp
                 | For "," For                                  [left]

    syntax Dec ::= "const" Id ":" TypeExp "=" Exp ";"
                 | "var" Id ":" TypeExp "=" Exp ";"
                 | Own
                 | "array" Id "[" Exp ":" Exp "]" ":" TypeExp ";"
                 | "record" Id "(" IdTypeExps ")" ";"
                 | "file" Id "withbuffer" Id ":" TypeExp ";"
                 | "proc" Id "(" IdTypeExps ")" Block
                 | "rec" "proc" Id "(" IdTypeExps ")" Block
                 | "func" Id "(" IdTypeExps ")" ":" TypeExp "{" Exp "}"
                 | "rec" "func" Id "(" IdTypeExps ")" ":" TypeExp "{" Exp "}"
    syntax Own                                                  [locations]
    syntax Own ::= "own" Id ":" TypeExp "=" Exp ";"
    syntax Ids ::= List{Id, ","}

    syntax Acc ::= Bool
                 | String
                 | Id
                 | "read"
                 | "this"
                 | Null
                 | "array" "[" Exp ":" Exp "]" ":" TypeExp
                 | "record" "(" IdTypeExps ")"
                 | "valof" ":" TypeExp Block
                 > left:
                   Acc "(" Exps ")"
                 | Acc "." Acc
                 | Acc "[" Exp "]"
    syntax Exp ::= Acc
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

    syntax TypeExp ::= "int"
                      | "float"
                      | "bool"
                      | "string"
                      | "array" "of" TypeExp
                      | "record" "(" IdTypeExps ")"
                      | "proc" "(" TypeExps ")"
                      | "func" "(" TypeExps ")" TypeExp
                      | "file" TypeExp
                      | "ref" TypeExp
                      | Id

    syntax TypeExps ::= List{TypeExp, ","}
    syntax IdTypeExp ::= Id ":" TypeExp
    syntax IdTypeExps ::= List{IdTypeExp, ","}
endmodule

// Syntax additional to the common syntax to complete the parsed syntax
module SMALL-SYNTAX-PARSED
    imports SMALL-SYNTAX-COMMON
    imports ALTINT-SYNTAX
    imports DOUBLE-SYNTAX

    syntax Com ::= "trap" "{" Decs Coms Escs "}"
    syntax Coms ::= List{Com, ""}
    syntax Esc ::= Id ":" Coms
    syntax Block ::= "{" Decs Coms "}"

    syntax Dec ::= "class" Id "{" SCDecs "}"
                 | "class" Id "extends" Id "{" SCDecs "}"
    syntax Decs ::= List{Dec, ""}

    syntax SCDec ::= "public" CDec
                   | "private" CDec
                   | CDec
    syntax SCDecs ::= List{SCDec, ""}

    syntax CDec ::= "const" Id ":" TypeExp "=" Exp ";"
                  | "var" Id ":" TypeExp "=" Exp ";"
                  | "file" Id "withbuffer" Id ":" TypeExp ";"
                  | "proc" Id "(" IdTypeExps ")" Block
                  | "func" Id "(" IdTypeExps ")" ":" TypeExp "{" Exp "}"
                  | "array" Id "[" Exp ":" Exp "]" ":" TypeExp ";"
                  | "record" Id "(" IdTypeExps ")" ";"

    syntax Acc ::= Int
                 | AltInt
                 | Double
                 | "new" Id "(" ")"
                 | "(" Exp ")"
endmodule

// Syntax additional to the common syntax to complete the extended syntax
module SMALL-SYNTAX
    imports SMALL-SYNTAX-COMMON
    imports FLOAT-SYNTAX
    imports MINT-SYNTAX

    syntax Com ::= "trap" Com Escs
                 | "Skip"
                 | Com Com                                      [right]
    syntax Esc ::= Id ":" Com
    syntax Block ::= "{" Dec Com "}"

    syntax Dec ::= "class" Id SCDec
                 | "class" Id "extends" Id SCDec
                 | "SkipDec"
                 | Dec Dec                                      [right]

    syntax SCDec ::= "public" Dec
                   | "private" Dec
                   | "SkipSCDec"
                   | SCDec SCDec                                [right]

    syntax Acc ::= MInt{64}
                 | Float
                 | "new" Exp
                 | brackets(Exp)
    syntax MInt{64}

    syntax TypeExp ::= typeInfer(Exp)
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

    // Remove trap's awkward syntax required to force the correct formatting
    rule trap { Ds Cs Escs } => trap { Ds Cs } Escs             [anywhere]

    // Covert CDecs in class to Decs
    rule class I { SCDs } => class I convertSCDecs(SCDs)        [anywhere]
    rule class I1 extends I2 { SCDs } => class I1 extends I2 convertSCDecs(SCDs)    [anywhere]

    // Convert Id in new to an Exp
    rule new I ( ) => new I                                     [anywhere]

    // Convert brackets
    rule ( E ):Exp => brackets(E)                               [anywhere]

    // Convert syntax that uses Coms or Decs to a version that does not
    rule `{__}_SMALL-SYNTAX-PARSED_Block_Decs_Coms`(Ds, Cs) =>
        `{__}_SMALL-SYNTAX_Block_Dec_Com`(convertDecs(Ds), convertComs(Cs)) [anywhere]
    rule `_:__SMALL-SYNTAX-PARSED_Esc_Id_Coms`(I, Cs) =>
        `_:__SMALL-SYNTAX_Esc_Id_Com`(I, convertComs(Cs))       [anywhere]

    // Convert uses of Coms to chains
    syntax Com ::= convertComs(Coms)                            [function]
    rule convertComs(C Cs) => C convertComs(Cs)
    rule convertComs(.Coms) => Skip

    // Convert uses of Decs to chains
    syntax Dec ::= convertDecs(Decs)                            [function]
    rule convertDecs(D Ds) => D convertDecs(Ds)
    rule convertDecs(.Decs) => SkipDec

    // Convert uses of SCDecs to chains
    syntax SCDec ::= convertSCDecs(SCDecs)                      [function]
    rule convertSCDecs(SCD SCDs) => convertSCDec(SCD) convertSCDecs(SCDs)
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