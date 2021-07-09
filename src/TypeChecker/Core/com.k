requires "additional-syntax.k"

module COM
    imports ADDITIONAL-SYNTAX

    // Assignment
    context HOLE = _ ;
    context _ = (HOLE => reval(HOLE)) ;
    rule T1 = T2 ; => .
        requires T2 assignable T1

    // Block
    rule <k> { D:Dec ; C:Com } => D ~> C ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>

    // Output
    context output (HOLE => reval(HOLE)) ;
    rule output T ; => .
        requires isPrintable(T)

    // Procedure
    context HOLE:Exp ( _:Exps ) ;
    context _:Exp ( HOLE:Exps ) ;                               [result(Types)]
    rule TProc Ts1 ( Ts2 ) ; => .
        requires Ts2 <=Types Ts1

    // If
    context if ( (HOLE => reval(HOLE)) ) _ else _
    rule if ( TBool ) C1 else C2 => C1 ~> C2

    // While
    context while ( (HOLE => reval(HOLE)) ) _
    rule while ( TBool ) C => C

    // Repeat
    context repeat _ until ( (HOLE => reval(HOLE)) )
    rule repeat C until ( TBool ) => C

    // For
    syntax KItem ::= for(Exp, For, Com)
    syntax For ::= forEval(For)
    context for(HOLE, _, _)
    context for(_, (HOLE => forEval(HOLE)), _)
    rule for ( I = F ) C => for(I, F, C)                        [structural]
    rule for(T1, T2, C) => C
        requires T2 assignable T1
    // for exp
    context forEval((HOLE => reval(HOLE)))
    // for while
    context forEval((HOLE => reval(HOLE)) while _)
    context forEval(_ while (HOLE => reval(HOLE)))
    rule forEval(T1:Type while TBool => T1)
    // for step
    context forEval((HOLE => reval(HOLE)) step _ until _)
    context forEval(_ step (HOLE => reval(HOLE)) until _)
    context forEval(_ step _ until (HOLE => reval(HOLE)))
    rule forEval(TInt step TInt until TInt => TInt)
    // for chain
    context forEval((HOLE => forEval(HOLE)) , _)
    context forEval(_ , (HOLE => forEval(HOLE)))
    rule forEval(T1 , T2 => T1)
        requires T1 ==K T2

    // Trap
    rule <k> trap C Escs => C ~> tenv(TEnv) ~> Escs ...</k>
         <tenv> TEnv => updateMap(TEnv, map(Escs)) </tenv>
    rule Esc:Esc Escs => Esc ~> Escs                            [structural]
    rule .Escs => .                                             [structural]
    rule _ :: C => C                                            [structural]

    // Escape
    syntax KItem ::= escape(Exp)
    context escape(HOLE)
    rule escapeto I ; => escape(I)
    rule escape(TEscape) => .

    // Return
    context return (HOLE => reval(HOLE)) ;
    rule <k> return T1 ; => . ...</k>
         <returnType> T2 </returnType>
            requires T1 <=Type T2

    // With Do
    context with (HOLE => reval(HOLE)) do _
    rule <k> with TRecord ITs do C => C ~> tenv(TEnv) ...</k>
         <tenv> TEnv => updateMap(TEnv, map(ITs)) </tenv>

    // Chain
    rule C1:Com ; C2 => C1 ~> C2                                [structural]

    // Skip
    rule Skip => .                                              [structural]
endmodule