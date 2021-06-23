requires "../configuration.k"
requires "../Core/additional-syntax.k"

module CLASSES
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX

    // Class
    syntax KItem ::= SCDecInterface(SCDec, Map, Map) // Scoped class declarations, public mapping, private mapping - produce class interface
                   | SCDec(SCDec, Int) // Scoped class declarations, class' object id - type check SCDs
                   | end(Id, Int, SCDec) // Identifier of class, classes object id, scoped class declarations - mark end of SCDecInterface
    // Type check the scoped class declarations then create the class, for now assumes the class has no mapping
    rule class I SCDs => createClass(I, !N, .Map) ~> SCDecInterface(SCDs, .Map, .Map) ~> end(I, !N, SCDs)

    // Turn the class declaration in the scoped class declaration into a map (what identifiers need to be bound to what
    // types), the class declarations will be properlly type checked later when the type of the class is known
    syntax Dec ::= Map
    syntax Dec ::= CDecInterface(Dec)
    context SCDecInterface(public (HOLE => CDecInterface(HOLE)), _, _)  [result(Map)]
    context SCDecInterface(private (HOLE => CDecInterface(HOLE)), _, _) [result(Map)]

    // Update either the public or private map accordingly and add the declaration that needs to be checked to the end
    rule SCDecInterface(public M' => SkipSCDec, M => updateMap(M, M'), _)
    rule SCDecInterface(private M' => SkipSCDec, _, M => updateMap(M, M'))

    // A chain of scoped class declaration involves checking the first one then checking the second one
    rule SCDecInterface(SCD1 ; SCD2, M1, M2) => SCDecInterface(SCD1, M1, M2) ~> SCDecInterface(SCD2, .Map, .Map)

    // A SkipDec can be emiminated from the front with the mappings and declarations to check later being carried forward
    rule SCDecInterface(SkipSCDec, M1, M2) ~> SCDecInterface(SCD, .Map, .Map) => SCDecInterface(SCD, M1, M2)

    // One the last scoped class declaration has been checked, check all the declarations with all the class mappings
    // then then remove the private mappings for the rest of the program
    rule <k> SCDecInterface(SkipSCDec, M1, M2) ~> end(I, N, SCDs) => createClass(I, N, updateMap(M1, M2)) ~> SCDec(SCDs, N) ~> createClass(I, N, M1) ~> setThis(This) ~> returnType(ReturnType) ...</k>
         <this> This => -1 </this>
         <returnType> ReturnType => TVoid </returnType>

    // Constant Interface
    context CDecInterface(const _ : (HOLE => teval(HOLE)) = _ ;)
    rule CDecInterface(const I : T1 = _ ; => I |-> T1)

    // Variable Interface
    context CDecInterface(var _ : (HOLE => teval(HOLE)) = _ ;)
    rule CDecInterface(var I : T1 = _ ; => I |-> refer(T1))
            requires refer(T1) =/=K TError

    // File Interface
    context CDecInterface(file _ withbuffer _ : (HOLE => teval(HOLE)) ;)
    rule CDecInterface(file I1 withbuffer I2 : T ; => updateMap(I2 |-> refer(T), I1 |-> refer(TFile T)))
            requires refer(T) =/=K TError

    // Procedure Interface
    context CDecInterface(proc _ ( HOLE ) _)                    [result(IdTypes)]
    rule CDecInterface(proc I ( ITs ) _ => I |-> TMethod TProc types(ITs))

    // Function Interface
    context CDecInterface(func _ ( HOLE ) : _ { _ })            [result(IdTypes)]
    context CDecInterface(func _ ( _ ) : (HOLE => teval(HOLE)) { _ })
    rule CDecInterface(func I ( ITs ) : T { _ } => I |-> TMethod TFunc types(ITs) T)

    // A chain of scoped class declaration involves checking the first one then checking the second one
    rule SCDec(SCD1 ; SCD2, N) => SCDec(SCD1, N) ~> SCDec(SCD2, N)

    // Public or private do not matter, just check the class declaration
    syntax KItem ::= CDec(Dec, Int)
    rule SCDec(public D, N) => CDec(D, N)
    rule SCDec(private D, N) => CDec(D, N)
    rule SCDec(SkipSCDec, _) => .

    // Procedure
    rule <k> CDec(proc I ( ITs ) C, N) => proc I ( ITs ) C ~> setThis(This) ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>
         <this> This => N </this>

    // Function
    rule <k> CDec(func I ( ITs ) : T { E }, N) => func I ( ITs ) : T { E } ~> setThis(This) ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>
         <this> This => N </this>

    // Other Class Declaration
    rule <k> CDec(D, _) => D ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>                                    [owise]

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

    syntax KItem ::= useThis(Int, K)
    rule <k> useThis(N, K) => K ~> setThis(This) ...</k>
         <this> This => N </this>

    syntax KItem ::= createClass(Id, Int, Map)
    rule <k> createClass(I, N, M) => . ...</k>
         <tenv> TEnv => TEnv[I <- TClass N M] </tenv>
         <classes> Classes => Classes[N <- TClass N M] </classes>
endmodule