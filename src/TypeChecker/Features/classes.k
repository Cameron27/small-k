requires "../configuration.k"
requires "../Core/additional-syntax.k"

module CLASSES
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX

    // Class
    syntax KItem ::= objSCDec(SCDec, Map, Map, Dec)
                   | createClass(Id, Int)
    rule <k> class I SCD => objSCDec(SCD, .Map, .Map, SkipDec) ~> createClass(I, !N) ...</k>
         <tenv> TEnv => TEnv[I <- TClass !N .Map] </tenv>
         <classes> Classes => Classes[!N <- TClass !N .Map] </classes>

    // Turn the declaration in the scoped class declaration into a map (the update that needs to be made) and optionally
    // a declaration (function/procedure body checking that need to be done)
    syntax ObjUpdateDec ::= Map "," Dec
                 | Map
    syntax Dec ::= ObjUpdateDec
    syntax Dec ::= objDec(Dec)
    context objSCDec(public (HOLE => objDec(HOLE)), _, _, _)    [result(ObjUpdateDec)]
    context objSCDec(private (HOLE => objDec(HOLE)), _, _, _)   [result(ObjUpdateDec)]

    // Update either the public or private map accordingly and add the declaration that needs to be checked to the end
    rule objSCDec(public M':Map , D':Dec => SkipSCDec, M => updateMap(M, M'), _, D => D ; D')
    rule objSCDec(private M':Map , D':Dec => SkipSCDec, _, M => updateMap(M, M'), D => D ; D')
    rule objSCDec(public M':Map => SkipSCDec, M => updateMap(M, M'), _, _)
    rule objSCDec(private M':Map => SkipSCDec, _, M => updateMap(M, M'), _)

    // Chain
    rule objSCDec(SCD1 ; SCD2, M1, M2, K) => objSCDec(SCD1, M1, M2, K) ~> objSCDec(SCD2, .Map, .Map, SkipDec)

    // Skip
    rule objSCDec(SkipSCDec, M1, M2, D) ~> objSCDec(SCD, .Map, .Map, SkipDec) => objSCDec(SCD, M1, M2, D)
    rule <k> objSCDec(SkipSCDec, M1, M2, D) ~> createClass(I, N) => D ~> removePrivate(I, N, M1) ~> setThis(This) ...</k>
         <tenv> TEnv => TEnv[I <- TClass N updateMap(M1, M2)] </tenv>
         <classes> Classes => Classes[N <- TClass N updateMap(M1, M2)] </classes>
         <this> This => N </this>

    // Constant
    context objDec(const _ : (HOLE => teval(HOLE)) = _ ;)
    context objDec(const _ : _ = (HOLE => reval(HOLE)) ;)
    rule objDec(const I : T1 = T2 ; => I |-> T1)
            requires T2 <=Type T1

    // Variable
    context objDec(var _ : (HOLE => teval(HOLE)) = _ ;)
    context objDec(var _ : _ = (HOLE => reval(HOLE)) ;)
    rule objDec(var I : T1 = T2 ; => I |-> refer(T1))
            requires T2 <=Type T1 andBool refer(T1) =/=K TError

    // File
    context objDec(file _ withbuffer _ : (HOLE => teval(HOLE)) ;)
    rule objDec(file I1 withbuffer I2 : T ; => updateMap(I2 |-> refer(T), I1 |-> refer(TFile T)))
            requires refer(T) =/=K TError

    // Procedure
    context objDec(proc _ ( HOLE ) _)                           [result(IdTypes)]
    rule objDec(proc I ( ITs ) C => I |-> TMethod TProc types(ITs) , proc I ( ITs ) C)

    // Function
    context objDec(func _ ( HOLE ) : _ { _ })                   [result(IdTypes)]
    context objDec(func _ ( _ ) : (HOLE => teval(HOLE)) { _ })
    rule objDec(func I ( ITs ) : T { E } => I |-> TMethod TFunc types(ITs) T , func I ( ITs ) : T { E })

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

    syntax KItem ::= removePrivate(Id, Int, Map)
    rule <k> removePrivate(I, N, M) => . ...</k>
         <tenv> TEnv => TEnv[I <- TClass N M] </tenv>
         <classes> Classes => Classes[N <- TClass N M] </classes>
endmodule