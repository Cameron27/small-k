requires "../Core/additional-syntax.k"
requires "default-environment.k"

module OWN
    imports K-LOCATIONS
    imports ADDITIONAL-SYNTAX
    imports DEFAULT-ENVIRONMENT

    // Own
    syntax FileLoc ::= fileLoc(Int, Int)
    // the location of the own declaration in the file is is used as the unique identifier for the declaration
    rule <k> #location(own I : _ = _ ;, _, SL, SC, _, _) => . ...</k>
         <env> Env => Env[I <- L] </env>
         <globalEnv>... fileLoc(SL, SC) |-> L ...</globalEnv>   [owise]

    syntax KItem ::= own(Com)
                   | own(For)
                   | own(Escs)
                   | own(Esc)
                   | own(Dec)
                   | own(SCDec)
                   | own(Exp)
                   | own(Exps)

    // Own
    syntax KItem ::= ownEval(FileLoc, Exp)
    rule own(#location(own _ : _ = E1 ;, _, SL, SC, _, _)) => own(E1) ~> ownEval(fileLoc(SL, SC), E1)
    context ownEval(_, (HOLE => reval(HOLE)))
    rule <k> ownEval(FL, E:Rv) => . ...</k>
         <globalEnv> GEnv => GEnv[FL <- Loc(!N)] </globalEnv>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Com
    rule own(E1 = E2 ;) => own(E1) ~> own(E2)
    rule own(output E1 ;) => own(E1)
    rule own(E1 ( Es ) ;) => own(E1) ~> own(Es)
    rule own(if ( E1 ) C1 else C2) => own(E1) ~> own(C1) ~> own(C2)
    rule own(while ( E1 ) C1) => own(E1) ~> own(C1)
    rule own(repeat C1 until ( E1 )) => own(C1) ~> own(E1)
    rule own(trap C1 Escs) => own(C1) ~> own(Escs)
    rule own(for ( _ = F1 ) C1) => own(F1) ~> own(C1)
    rule own(escapeto _ ;) => .
    rule own(return E1 ;) => own(E1)
    rule own(with E1 do C1) => own(E1) ~> own(C1)
    rule own(C1:Com C2) => own(C1) ~> own(C2)
    rule own(Skip) => .

    // For
    rule own((E1:Exp):For) => own(E1:Exp)
    rule own(E1 while E2) => own(E1) ~> own(E2)
    rule own(E1 step E2 until E3) => own(E1) ~> own(E2) ~> own(E3)
    rule own(F1:For , F2) => own(F1) ~> own(F2)

    // Escs/Esc
    rule own(Esc:Esc Escs) => own(Esc) ~> own(Escs)
    rule own(.Escs) => .
    rule own(_ : C1) => own(C1)

    // Dec
    rule own(const _ : _ = E1 ;) => own(E1)
    rule own(var _ : _ = E1 ;) => own(E1)
    rule own(array _ [ E1 : E2 ] : _ ;) => own(E1) ~> own(E2)
    rule own(record _ ( _ ) ;) => .
    rule own(file _ withbuffer _ : _ ;) => .
    rule own(proc _ ( _ ) C1) => own(C1)
    rule own(rec proc _ ( _ ) C1) => own(C1)
    rule own(func _ ( _ ) : _ { E1 }) => own(E1)
    rule own(rec func _ ( _ ) : _ { E1 }) => own(E1)
    rule own(class _ SCD1) => own(SCD1)
    rule own(class _ extends _ SCD1) => own(SCD1)
    rule own({ C1 D1 }) => own(C1) ~> own(D1)
    rule own(D1:Dec D2) => own(D1) ~> own(D2)
    rule own(SkipDec) => .

    // SCDec
    rule own(public D1) => own(D1)
    rule own(private D1) => own(D1)
    rule own(SkipSCDec) => .
    rule own(SCD1:SCDec SCD2) => own(SCD1) ~> own(SCD2)

    // Exp
    rule own(array [ E1 : E2 ] : _) => own(E1) ~> own(E2)
    rule own(valof : _ C1) => own(C1)
    rule own(E1:Acc ( Es )) => own(E1) ~> own(Es)
    rule own(E1 . E2) => own(E1) ~> own(E2)
    rule own(E1 [ E2 ]) => own(E1) ~> own(E2)
    rule own(cont E1) => own(E1)
    rule own(ref E1) => own(E1)
    rule own(! E1) => own(E1)
    rule own(+ E1) => own(E1)
    rule own(- E1) => own(E1)
    rule own(E1 * E2) => own(E1) ~> own(E2)
    rule own(E1 / E2) => own(E1) ~> own(E2)
    rule own(E1 % E2) => own(E1) ~> own(E2)
    rule own(E1 + E2) => own(E1) ~> own(E2)
    rule own(E1 - E2) => own(E1) ~> own(E2)
    rule own(E1 < E2) => own(E1) ~> own(E2)
    rule own(E1 <= E2) => own(E1) ~> own(E2)
    rule own(E1 > E2) => own(E1) ~> own(E2)
    rule own(E1 >= E2) => own(E1) ~> own(E2)
    rule own(E1 == E2) => own(E1) ~> own(E2)
    rule own(E1 != E2) => own(E1) ~> own(E2)
    rule own(E1 & E2) => own(E1) ~> own(E2)
    rule own(E1 ^ E2) => own(E1) ~> own(E2)
    rule own(E1 | E2) => own(E1) ~> own(E2)
    rule own(E1 ? E2 : E3) => own(E1) ~> own(E2) ~> own(E3)
    rule own(brackets(E)) => own(E)
    rule own(_:Exp) => .                                        [owise] // All other expressions

    // Exps
    rule own(E1:Exp , Es:Exps) => own(E1) ~> own(Es)
    rule own(.Exps) => .
endmodule