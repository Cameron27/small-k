requires "../configuration.k"
requires "additional-syntax.k"
requires "../Features/default-environment.k"

module DEC
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX
    imports K-LOCATIONS
    imports DEFAULT-ENVIRONMENT

    // Constant
    context const _ : HOLE = _ ;
    context const _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> const I : T1 = T2 ; => . ...</k>
         <tenv> TEnv => TEnv[I <- T1] </tenv>
            requires T1 ==Type T2

    // Variable
    context var _ : HOLE = _ ;
    context var _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> var I : T1 = T2 ; => . ...</k>
         <tenv> TEnv => TEnv[I <- refer(T1)] </tenv>
            requires T1 ==Type T2 andBool refer(T1) =/=K TError

    // Own
    context own _ : HOLE = _ ;
    context own _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> #location(O:Own, _, _, _, _, _) => O ~> tenv(TEnv) ...</k>
         <tenv> TEnv => defaultEnvironment() </tenv>            [structural]
    rule <k> own I : T1 = T2 ; ~> tenv(TEnv) => . ...</k>
         <tenv> _ => TEnv[I <- refer(T1)] </tenv>
            requires T1 ==Type T2 andBool refer(T1) =/=K TError

    // File
    context file _ withbuffer _ : HOLE ;
    rule <k> file I1 withbuffer I2 : T ; => . ...</k>
         <tenv> TEnv => TEnv[I2 <- refer(T)][I1 <- refer(TFile T)] </tenv>
            requires refer(T) =/=K TError

    // Procedure
    context proc _ ( HOLE ) _                                   [result(IdTypes)]
    rule <k> proc I ( ITs ) C => C ~> tenv(TEnv[I <- TProc types(ITs)]) ...</k>
         <tenv> TEnv => updateMap(TEnv, map(ITs)) </tenv>

    // Recursive Procedure
    context rec proc _ ( HOLE ) _                               [result(IdTypes)]
    rule <k> rec proc I ( ITs ) C => C ~> tenv(TEnv[I <- TProc types(ITs)]) ...</k>
         <tenv> TEnv => updateMap(TEnv, map( I : TProc types(ITs) ,, ITs)) </tenv>

    // Function
    context func _ ( HOLE ) : _ { _ }                           [result(IdTypes)]
    context func _ ( _ ) : HOLE { _ }
    rule <k> func I ( ITs ) : T { E } => E ~> funcTest(T) ~> tenv(TEnv[I <- TFunc types(ITs) T]) ...</k>
         <tenv> TEnv => updateMap(TEnv, map(ITs)) </tenv>
    syntax KItem ::= funcTest(Type)
    rule T1 ~> funcTest(T2) => .
        requires T1 ==Type T2

    // Recursive Function
    context rec func _ ( HOLE ) : _ { _ }                       [result(IdTypes)]
    context rec func _ ( _ ) : HOLE { _ }
    rule <k> rec func I ( ITs ) : T { E } => E ~> funcTest(T) ~> tenv(TEnv[I <- TFunc types(ITs) T]) ...</k>
         <tenv> TEnv => updateMap(TEnv, map( I : TFunc types(ITs) T ,, ITs)) </tenv>

    // Chain
    rule D1:Dec ; D2 => D1 ~> D2                                [structural]

    // Skip
    rule SkipDec => .
endmodule