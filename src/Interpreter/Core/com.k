requires "additional-syntax.k"
requires "../configuration.k"
requires "../../Common/helper.k"

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
    rule <k> output E:MInt{64} ; => . ...</k>
         <out> List => List ListItem(MInt2Signed(E)) ListItem("\n") </out>
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
    context _:Ev ( HOLE ) ;                                     [result(Evs)]
    // enter procedure
    rule <k> proc(Is, env(Env'), C) ( Es ) ; ~> Rest => params(Is, Es) ~> C ~> pop() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
            requires isDvs(Es)

    // Recursive Procedure
    rule recProc(Is, Env, C) ( Es ) ;
            => proc(Is, Env, C) ( recProc(Is, Env, C) , Es ) ;  [structural]

    // If
    context if ( HOLE => reval(HOLE) ) _ else _
    rule if ( true ) C else _ => C
    rule if ( false ) _ else C => C

    // While
    rule while (E) C => if (E) (C ; while (E) C)                [structural]

    // Repeat
    rule repeat C until ( E ) =>  C ~> if (! E) repeat C until (E)  [structural]

    // Trap
    syntax KItem ::= escs(Escs, Int)
                   | esc(Esc, Int)
    // enter trap
    rule <k> trap C Escs ~> Rest => escs(Escs, !N) ~> C ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>
    // setup traps to be assigned last to first
    rule <k> escs((I :: Cs Escs), N) => escs(Escs, N) ~> esc(I :: Cs, N) ...</k>    [structural]
    rule escs(.Escs, _) => .                                    [structural]
    // add lables to environment
    syntax Dv ::= trapLabel(Com, Int)
    rule <k> esc(I :: Cs, N) => . ...</k>
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
    rule <k> return E:Ev ; ~> _ => Env ~> E ~> Rest </k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> return _:Ev ; ...</k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M

    // With Do
    context with (HOLE => reval(HOLE)) do _
    rule <k> with record(REnv) do C ~> Rest => C ~> pop() </k>
         <env> Env => updateMap(Env, REnv) </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>

    // Block
    rule <k> { D:Dec ; C:Com } ~> Rest => D ~> C ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>   [structural]

    // Chain
    rule C1:Com ; C2 => C1 ~> C2                                [structural]

    // Skip
    rule Skip => .                                              [structural]
endmodule