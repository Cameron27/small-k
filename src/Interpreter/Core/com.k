requires "additional-syntax.k"
requires "../../Common/helper.k"

module COM
    imports ADDITIONAL-SYNTAX
    imports HELPER

    // Assign
    context HOLE = _ ;
    context _:Loc = (HOLE => reval(HOLE)) ;
    rule <k> L:Loc = E:Rv ; => . ...</k>
         <store> Store => Store[L <- E] </store>

    // Output
    context output (HOLE => reval(HOLE)) ;
    rule <k> output E:MInt{64} ; => . ...</k>
         <out>... .List => ListItem(MInt2Signed(E)) ListItem("\n") </out>
    rule <k> output E:Float ; => . ...</k>
         <out>... .List => ListItem(printFloat(E)) ListItem("\n") </out>
    rule <k> output Loc(I) ; => . ...</k>
         <out>... .List => ListItem("Loc(" +String Int2String(I) +String ")") ListItem("\n") </out>
    rule <k> output true ; => . ...</k>
         <out>... .List => ListItem("true") ListItem("\n") </out>
    rule <k> output false ; => . ...</k>
         <out>... .List => ListItem("false") ListItem("\n") </out>
    rule <k> output E:Rv ; => . ...</k>
         <out>... .List => ListItem(E) ListItem("\n") </out>    [owise]

    // Procedure
    context HOLE ( _ ) ;
    context _:Ev ( HOLE ) ;                                     [result(Evs)]
    // enter procedure
    rule <k> proc(Is, env(Env'), C) ( Es ) ; => params(Is, Es) ~> C ~> env(Env) ...</k>
         <env> Env => Env' </env>
            requires isDvs(Es)

    // Recursive Procedure
    rule recProc(Is, Env, C) ( Es ) ;
            => proc(Is, Env, C) ( recProc(Is, Env, C) , Es ) ;  [structural]

    // If
    context if ( HOLE => reval(HOLE) ) _ else _
    rule if ( true ) C else _ => C
    rule if ( false ) _ else C => C

    // While
    rule while (E) C => if (E) (C while (E) C)                  [structural]

    // Repeat
    rule repeat C until ( E ) =>  C ~> if (! E) repeat C until (E)  [structural]

    // Trap
    syntax KItem ::= escs(Escs, K, Env)
                   | esc(Esc, K, Env)
    // enter trap
    rule <k> trap C Escs ~> Rest => escs(Escs, Rest, env(Env)) ~> C ~> env(Env) ~> Rest </k>
         <env> Env </env>
    // setup traps to be assigned last to first
    rule <k> escs((I : Cs Escs), K, Env) => escs(Escs, K, Env) ~> esc(I : Cs, K, Env) ...</k>   [structural]
    rule escs(.Escs, _, _) => .                                 [structural]
    // add lables to environment
    rule <k> esc(I : Cs, K, Env') => . ...</k>
         <env> Env => Env[I <- cc(Cs ~> K, Env')] </env>
    // resolve an encountered escapeto
    rule <k> escapeto I ; ~> _ => Cc </k>
         <env>... I |-> Cc:Cc ...</env>

    // Return
    context return (HOLE => reval(HOLE)) ;
    // resolve an encounted return
    rule <k> return E:Ev ; ~> _ => E ~> Ec </k>
         <env>... "return" |-> Ec ...</env>

    // With Do
    context with (HOLE => reval(HOLE)) do _
    rule <k> with record(REnv) do C => C ~> env(Env) ...</k>
         <env> Env => updateMap(Env, REnv) </env>

    // Block
    rule <k> { D:Dec C:Com } => D ~> C ~> env(Env) ...</k>
         <env> Env </env>                                       [structural]

    // Chain
    rule C1:Com C2 => C1 ~> C2                                  [structural]

    // Skip
    rule Skip => .                                              [structural]
endmodule