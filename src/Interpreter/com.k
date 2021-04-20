requires "additional-syntax.k"
requires "configuration.k"
requires "../Common/helper.k"

module COM
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION
    imports HELPER

    // Assign
    context HOLE = _ ;
    context _:Loc = (HOLE => reval(HOLE)) ;
    rule <k> L:Loc = E:Rv ; => . ...</k>
         <store> Store => Store[L <- E] </store>

    // Output
    context output (HOLE => reval(HOLE)) ;
    rule <k> output E:Float ; => . ...</k>
         <out> List => List ListItem(printFloat(E)) ListItem("\n") </out>
    rule <k> output Loc(I) ; => . ...</k>
         <out> List => List ListItem("Loc(" +String Int2String(I) +String ")") ListItem("\n") </out>
    rule <k> output true ; => . ...</k>
         <out> List => List ListItem("true") ListItem("\n") </out>
    rule <k> output false ; => . ...</k>
         <out> List => List ListItem("false") ListItem("\n") </out>
    rule <k> output E:Rv ; => . ...</k>
         <out> List => List ListItem(E) ListItem("\n") </out>   [owise]

    // Procedure
    context HOLE ( _ ) ;
    context _:Dv ( HOLE ) ;                                     [result(Dvs)]
    // enter procedure
    rule <k> proc(Is, env(Env'), C) ( Es ) ; ~> Rest => params(Is, Es) ~> C ~> pop() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
            requires isDvs(Es)

    // Recursive Procedure
    rule recProc(Is, Env, C) ( Es ) ;
            => proc(Is, Env, C) ( recProc(Is, Env, C) , Es ) ;  [structural]

    // If
    context if ( HOLE => reval(HOLE) ) _
    rule if ( true ) C => C
    rule if ( false ) _ => .
    context if ( HOLE => reval(HOLE) ) _ else _
    rule if ( true ) C else _ => C
    rule if ( false ) _ else C => C

    // While
    rule while (E) C => if (E) { .Decs C while (E) C }          [structural]

    // Repeat
    rule repeat C until ( E ) =>  C ~> if (! E) repeat C until (E)  [structural]

    // For
    // for expression
    context for ( _ = (HOLE => reval(HOLE)) ) _
    rule <k> for ( I = E:Rv ) C => C ...</k>
         <env>... I |-> L:Loc ...</env>
         <store> Store => Store[L <- E] </store>
    // for while
    syntax KItem ::= whileFor(Loc, Exp, Exp, K)
    context whileFor(_, (HOLE => reval(HOLE)), _, _)
    context whileFor(_, _:Rv, (HOLE => reval(HOLE)), _)
    rule <k> for ( I = E1 while E2 ) C => whileFor(L, E1, E2, C ~> for ( I = E1 while E2 ) C) ...</k>
         <env>... I |-> L ...</env>
            requires isLoc(L)                                   [structural]
    rule <k> whileFor(L, E:Rv, true, C) => C ...</k>
         <store> Store => Store[L <- E] </store>
    rule whileFor(_, _:Rv, false, _) => .
    // for step
    syntax KItem ::= stepFor(Loc, Int, Exp, Exp, Com, Com)
                   | insertN(Int, Com)
    context for ( _ = (HOLE => reval(HOLE)) step _ until _ ) _
    context stepFor(_, _, (HOLE => reval(HOLE)), _, _, _)
    context stepFor(_, _, _:Rv, (HOLE => reval(HOLE)), _, _)
    rule <k> for ( I = N:Int step E1 until E2 ) C => stepFor(L, N, E1, E2, C, for ( I = N step E1 until E2 ) C) ...</k>
         <env>... I |-> L ...</env>
            requires isLoc(L)                                   [structural]
    rule <k> stepFor(L, N:Int, N1:Int, N2:Int, C1, C2) => C1 ~> insertN(N +Int N1, C2) ...</k>
         <store> Store => Store[L <- N] </store>
            requires ((N -Int N2) *Int sign(N1)) <Int 1
    rule stepFor(_, _:Int, _:Int, _:Int, _, _) => .             [owise]
    rule insertN(N, for ( I = _ step E1 until E2 ) C ) => for ( I = N step E1 until E2 ) C
    // for chain
    rule <k> for ( I = F1 , F2 ) C => for ( I = F1 ) C ~> for ( I = F2 ) C ...</k>

    // Trap
    syntax KItem ::= escs(Escs, Int)
                   | esc(Esc, Int)
    // enter trap
    rule <k> trap { Ds Cs Escs } ~> Rest => escs(Escs, !N) ~> { Ds Cs } ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>
    // setup traps to be assigned last to first
    rule <k> escs((I : Cs Escs), N) => escs(Escs, N) ~> esc(I : Cs, N) ...</k>  [structural]
    rule escs(.Escs, _) => .                                    [structural]
    // add lables to environment
    syntax KItem ::= trapLabel(Coms, Int)
    rule <k> esc(I : Cs, N) => . ...</k>
         <env> Env => Env[I <- trapLabel(Cs, N)] </env>
    // resolve an encountered escapeto
    rule <k> escapeto I ; ~> _ => Env ~> Cs ~> Rest </k>
         <env>... I |-> trapLabel(Cs, N) ...</env>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> escapeto I ;  ...</k>
         <env>... I |-> trapLabel(_, N) ...</env>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M                                 [structural]

    // Return
    context return (HOLE => reval(HOLE)) ;
    // resolve an encounted return
    rule <k> return E:Dv ; ~> _ => Env ~> E ~> Rest </k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> return _:Dv ; ...</k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M

    // With Do
    context with (HOLE => reval(HOLE)) do _
    rule <k> with record(REnv) do C ~> Rest => C ~> pop() </k>
         <env> Env => updateMap(Env, REnv) </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>

    // Block
    rule <k> { D:Decs C:Coms } ~> Rest => D ~> C ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>   [structural]

    rule C:Com Cs:Coms => C ~> Cs                               [structural]
    rule .Coms => .                                             [structural]
endmodule