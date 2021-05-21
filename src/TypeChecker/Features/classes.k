requires "../configuration.k"
requires "../Core/additional-syntax.k"

module CLASSES
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX

    // Class
    syntax KItem ::= objDec(Dec, Map, Dec)
                   | createClass(Id, Int)
    rule <k> class I CD => objDec(CD, .Map, SkipDec) ~> createClass(I, !N) ...</k>
         <tenv> TEnv => TEnv[I <- TClass !N .Map] </tenv>
         <classes> Classes => Classes[!N <- TClass !N .Map] </classes>

    // Constant
    context objDec(const _ : (HOLE => teval(HOLE)) = _ ;, _, _)
    context objDec(const _ : _ = (HOLE => reval(HOLE)) ;, _, _)
    rule objDec(const I : T1 = T2 ; => SkipDec, M => M[I <- T1], _)
            requires T2 <=Type T1

    // Variable
    context objDec(var _ : (HOLE => teval(HOLE)) = _ ;, _, _)
    context objDec(var _ : _ = (HOLE => reval(HOLE)) ;, _, _)
    rule objDec(var I : T1 = T2 ; => SkipDec, M => M[I <- refer(T1)], _)
            requires T2 <=Type T1 andBool refer(T1) =/=K TError

    // File
    context objDec(file _ withbuffer _ : (HOLE => teval(HOLE)) ;, _, _)
    rule objDec(file I1 withbuffer I2 : T ; => SkipDec, M => M[I2 <- refer(T)][I1 <- refer(TFile T)], _)
            requires refer(T) =/=K TError

    // Procedure
    context objDec(proc _ ( HOLE ) _, _, _)                     [result(IdTypes)]
    rule objDec(proc I ( ITs ) C => SkipDec, M => M[I <- TMethod TProc types(ITs)], D => D ; proc I ( ITs ) C)

    // Function
    context objDec(func _ ( HOLE ) : _ { _ }, _, _)             [result(IdTypes)]
    context objDec(func _ ( _ ) : (HOLE => teval(HOLE)) { _ }, _, _)
    rule objDec(func I ( ITs ) : T { E } => SkipDec , M => M[I <- TMethod TFunc types(ITs) T], D => D ; func I ( ITs ) : T { E })

    // Chain
    rule objDec(CD1 ; CD2, M, K) => objDec(CD1, M, K) ~> objDec(CD2, .Map, SkipDec)

    // Skip
    rule objDec(SkipDec, M, D) ~> objDec(CD, .Map, SkipDec) => objDec(CD, M, D)
    rule <k> objDec(SkipDec, M, D) ~> createClass(I, N) => D ~> setThis(This) ...</k>
         <tenv> TEnv => TEnv[I <- TClass N M] </tenv>
         <classes> Classes => Classes[N <- TClass N M] </classes>
         <this> This => N </this>

    // This
    rule <k> this => TObject This ...</k>
         <this> This </this>

    // Dot
    rule <k> TObject N . E => E ~> tenvTypeMethod(TEnv) ...</k>
         <tenv> TEnv => updateMap(TEnv, C) </tenv>
         <classes>... N |-> TClass _ C ...</classes>
    syntax TEnv ::= tenvTypeMethod(Map)
    rule <k> TMethod T ~> tenvTypeMethod(TEnv) => T ...</k>
         <tenv> _ => TEnv </tenv>
    rule <k> T:Type ~> tenvTypeMethod(TEnv) => T ...</k>
         <tenv> _ => TEnv </tenv>                               [owise]

    // New
    context new HOLE
    rule new TClass N _ => TObject N

    // Null
    rule null => TNull

    // Auxilary Functions

    // use to set this
    syntax KItem ::= setThis(Int)
    rule <k> setThis(This) => . ...</k>
         <this> _ => This </this>
endmodule