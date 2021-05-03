requires "../configuration.k"
requires "../Core/additional-syntax.k"
requires "../../Common/helper.k"

module FOR
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX
    imports HELPER

    // For Expression
    context for ( _ = (HOLE => reval(HOLE)) ) _
    rule <k> for ( I = E:Rv ) C => C ...</k>
         <env>... I |-> L:Loc ...</env>
         <store> Store => Store[L <- E] </store>

    // While
    syntax KItem ::= whileFor(Loc, Exp, Exp, K)
    context whileFor(_, (HOLE => reval(HOLE)), _, _)
    context whileFor(_, _:Rv, (HOLE => reval(HOLE)), _)
    rule <k> for ( I = E1 while E2 ) C => whileFor(L, E1, E2, C ~> for ( I = E1 while E2 ) C) ...</k>
         <env>... I |-> L ...</env>
            requires isLoc(L)                                   [structural]
    rule <k> whileFor(L, E:Rv, true, C) => C ...</k>
         <store> Store => Store[L <- E] </store>
    rule whileFor(_, _:Rv, false, _) => .

    // Step
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

    // Chain
    rule <k> for ( I = F1 , F2 ) C => for ( I = F1 ) C ~> for ( I = F2 ) C ...</k>

endmodule