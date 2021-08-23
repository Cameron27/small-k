requires "../Core/additional-syntax.k"
requires "default-environment.k"

module CLASSES
    imports ADDITIONAL-SYNTAX
    imports DEFAULT-ENVIRONMENT
    imports ID

    // Class
    syntax KItem ::= SCDecInterface(SCDec, Map, Map) // Scoped class declarations, public mapping, private mapping - produce class interface
                   | SCDec(SCDec, Int) // Scoped class declarations, class id - type check SCDs
                   | end(Id, Int, SCDec) // Identifier of class, class id, scoped class declarations - mark end of SCDecInterface
                   | end(Id, Int, SCDec, Type) // Identifier of class, class id, scoped class declarations, parent class - mark end of SCDecInterface
    // Type check the scoped class declarations then create the class, for now assumes the class has no mapping
    rule class I SCDs => createClass(I, !O, -1, .Map, .Map) ~> SCDecInterface(SCDs, .Map, .Map) ~> end(I, !O, SCDs)
    rule <k> class I1 extends I2 SCDs => createClass(I1, !N, -1, .Map, .Map) ~> SCDecInterface(SCDs, .Map, .Map) ~> end(I1, !N, SCDs, TClass O1 O2 Epub Epriv) ...</k>
         <tenv>... I2 |-> TClass O1 O2 Epub Epriv ...</tenv>

    // Turn the class declaration in the scoped class declaration into a map (what identifiers need to be bound to what
    // types), the class declarations will be properlly type checked later when the type of the class is known
    syntax Dec ::= Map
    syntax Dec ::= CDecInterface(Dec)
    context SCDecInterface(public (HOLE => CDecInterface(HOLE)), _, _)  [result(Map)]
    context SCDecInterface(private (HOLE => CDecInterface(HOLE)), _, _) [result(Map)]

    // Update either the public or private map accordingly and add the declaration that needs to be checked to the end
    rule SCDecInterface(public Epub' => SkipSCDec, Epub => updateMap(Epub, Epub'), _)
    rule SCDecInterface(private Epriv' => SkipSCDec, _, Epriv => updateMap(Epriv, Epriv'))

    // A chain of scoped class declaration involves checking the first one then checking the second one
    rule SCDecInterface(SCD1 SCD2, Epub, Epriv) => SCDecInterface(SCD1, Epub, Epriv) ~> SCDecInterface(SCD2, .Map, .Map)

    // A SkipDec can be emiminated from the front with the mappings and declarations to check later being carried forward
    rule SCDecInterface(SkipSCDec, Epub, Epriv) ~> SCDecInterface(SCD, .Map, .Map) => SCDecInterface(SCD, Epub, Epriv)

    // Once the last scoped class declaration has been checked, check all the declarations with all the class mappings
    // then remove the private mappings for the rest of the program
    rule <k> SCDecInterface(SkipSCDec, Epub, Epriv) ~> end(I, O, SCDs) =>
            createClass(I, O, -1, updateMap(Epub, Epriv), Epriv) ~>
            SCDec(SCDs, O) ~>
            createClass(I, O, -1, Epub, Epriv) ~>
            setThis(This) ~>
            setReturnType(ReturnType) ...</k>
         <this> This => -1 </this>
         <returnType> ReturnType => TVoid </returnType>
            requires size(intersectSet(keys(Epub), keys(Epriv))) ==Int 0
    // Same as above except for a class which extends another class
    rule <k> SCDecInterface(SkipSCDec, Epub, Epriv) ~> end(I, O1, SCDs, TClass O2 _ E2pub E2priv) =>
            createClass(I, O1, O2, updateMap(updateMap(E2pub, Epub), Epriv), updateMap(E2priv, Epriv)) ~>
            SCDec(SCDs, O1) ~>
            createClass(I, O1, O2, updateMap(E2pub, Epub), updateMap(E2priv, Epriv)) ~>
            setThis(This) ~>
            setReturnType(ReturnType) ...</k>
         <this> This => -1 </this>
         <returnType> ReturnType => TVoid </returnType>
            requires
                size(intersectSet(keys(Epub) |Set keys(E2pub), keys(Epriv) |Set keys(E2priv))) ==Int 0 andBool
                size(intersectSet(keys(Epriv), keys(E2priv))) ==Int 0 andBool
                allSubset(intersectSet(keys(Epub), keys(E2pub)), Epub, E2pub)

    // Constant Interface
    context CDecInterface(const _ : (HOLE => teval(HOLE)) = _ ;)
    rule CDecInterface(const I : T1:Type = _ ; => I |-> T1)

    // Variable Interface
    context CDecInterface(var _ : (HOLE => teval(HOLE)) = _ ;)
    rule CDecInterface(var I : T1:Type = _ ; => I |-> refer(T1))
        requires refer(T1) =/=K TError

    // Array Interface
    context CDecInterface(array _ [ _ : _ ] : (HOLE => teval(HOLE)) ;)
    rule CDecInterface(array I [ _ : _ ] : T:Type ; => I |-> TArray TRef T)

    // Record Interface
    context CDecInterface(record _ ( HOLE ) ;)                  [result(IdTypes)]
    rule CDecInterface(record I ( ITs:IdTypes ) ; => I |-> TRecord referAll(ITs))
        requires allDifferent(ids(ITs)) andBool referAll(ITs) =/=K ITError

    // File Interface
    context CDecInterface(file _ withbuffer _ : (HOLE => teval(HOLE)) ;)
    rule CDecInterface(file I1 withbuffer I2 : T:Type ; => updateMap(I2 |-> refer(T), I1 |-> refer(TFile T)))
        requires refer(T) =/=K TError

    // Procedure Interface
    context CDecInterface(proc _ ( HOLE ) _)                    [result(IdTypes)]
    rule CDecInterface(proc I ( ITs:IdTypes ) _ => I |-> TProc types(ITs))

    // Function Interface
    context CDecInterface(func _ ( HOLE ) : _ { _ })            [result(IdTypes)]
    context CDecInterface(func _ ( _:IdTypes ) : (HOLE => teval(HOLE)) { _ })
    rule CDecInterface(func I ( ITs:IdTypes ) : T:Type { _ } => I |-> TFunc types(ITs) T)

    // A chain of scoped class declaration involves checking the first one then checking the second one
    rule SCDec(SCD1 SCD2, N) => SCDec(SCD1, N) ~> SCDec(SCD2, N)

    // Public or private do not matter, just check the class declaration
    syntax KItem ::= CDec(Dec, Int)
    rule SCDec(public D, O) => CDec(D, O)
    rule SCDec(private D, O) => CDec(D, O)
    rule SCDec(SkipSCDec, _) => .

    // Procedure
    rule <k> CDec(proc I ( ITs ) C, O) => proc I ( ITs ) C ~> setThis(This) ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>
         <this> This => O </this>

    // Function
    rule <k> CDec(func I ( ITs ) : T { E }, O) => func I ( ITs ) : T { E } ~> setThis(This) ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>
         <this> This => O </this>

    // Other Class Declaration
    rule <k> CDec(D, _) => D ~> tenv(TEnv) ...</k>
         <tenv> TEnv </tenv>                                    [owise]

    // This
    rule <k> this => TObject This ...</k>
         <this> This </this>

    // Dot
    rule <k> TObject N . E => E ~> tenvType(TEnv) ...</k>
         <tenv> TEnv => updateMap(TEnv, C) </tenv>
         <classes>... N |-> TClass _ _ C _ ...</classes>

    // New
    context new HOLE
    rule new TClass O _ _ _ => TObject O

    // Null
    rule null => TNull

    // Update default environment
    rule defaultEnvironment(List => List ListItem(2), Env => Env
        String2Id("isNull") |-> TFunc (TUnion (TRef TObjectAny ,, TObjectAny) ,, .Types) TBool)
        requires notBool 2 in List

    // Auxilary Functions

    // Use to set this
    syntax KItem ::= setThis(Int)
    rule <k> setThis(This) => . ...</k>
         <this> _ => This </this>

    syntax KItem ::= useThis(Int, K)
    rule <k> useThis(N, K) => K ~> setThis(This) ...</k>
         <this> This => N </this>

    syntax KItem ::= createClass(Id, Int, Int, Map, Map)
    rule <k> createClass(I, O1, O2, Epub, Epriv) => . ...</k>
         <tenv> TEnv => TEnv[I <- TClass O1 O2 Epub Epriv] </tenv>
         <classes> Classes => Classes[O1 <- TClass O1 O2 Epub Epriv] </classes>
endmodule