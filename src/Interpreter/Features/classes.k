requires "../Core/additional-syntax.k"
requires "../helper.k"
requires "default-environment.k"

module CLASSES
    imports ADDITIONAL-SYNTAX
    imports INTERPRETER-HELPER
    imports DEFAULT-ENVIRONMENT

    // Class
    rule <k> class I SCD => . ...</k>
         <env> Env => Env[I <- class(I, !_, SCD, env(Env["return" <- undef]))] </env>

    syntax KItem ::= objDec(Dec)
    rule public CD => objDec(CD)
    rule private CD => objDec(CD)

    // Chain
    rule SCD1:SCDec SCD2 => SCD1 ~> SCD2                        [structural]
    rule O:Object ~> SCD:SCDec => SCD ~> O                      [structural]
    rule obj(M1) ~> obj(M2) => obj(updateMap(M2, M1))

    // Skip
    rule SkipSCDec => .

    // Constant
    context objDec(const _ : _ = (HOLE => reval(HOLE)) ;)
    rule objDec(const I : _ = E:Rv ;) => obj(I |-> E)

    // Variable
    context objDec(var _ : _ = (HOLE => reval(HOLE)) ;)
    rule <k> objDec(var I : _ = E:Rv ;) => obj(I |-> Loc(!N)) ...</k>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Array
    context objDec(array _ [ HOLE => reval(HOLE) : _ ] : _ ;)
    context objDec(array _ [ _:Ev : HOLE => reval(HOLE) ] : _ ;)
    syntax Dec ::= createArrayLocs(Id, Array, Int)
    rule objDec(array I [ N1:MInt{64} : N2:MInt{64} ] : _ ; => createArrayLocs(I, array(N1, N2, .List), MInt2Signed(N2) -Int MInt2Signed(N1) +Int 1))
        requires N2 >=sMInt N1                                  [structural]
    rule objDec(createArrayLocs(_, array(_, _, List => ListItem(Loc(!_N)) List), N => N -Int 1))
        requires N >Int 0
    rule objDec(createArrayLocs(I, Array, 0)) => obj(I |-> Array)

    // Record
    syntax Dec ::= createRecordLocs(Id, Record, Ids)
    rule objDec(record I ( ITs ) ; => createRecordLocs(I, record(.Map), IdTypeExps2Ids(ITs)))   [structural]
    rule objDec(createRecordLocs(_, record(Map => Map[I <- Loc(!_N)]), (I , Is) => Is))
    rule objDec(createRecordLocs(I, Record:Record, .Ids)) => obj(I |-> Record)

    // File
    rule <k> objDec(file F withbuffer B : _ ;) => obj(updateMap(B |-> Loc(!B), F |-> Loc(!F))) ...</k>
         <store> Store => Store[Loc(!F) <- file(.List, 1, Loc(!B))] </store>

    // Procedure
    rule <k> objDec(proc I(ITs) C) => obj(I |-> method(proc(IdTypeExps2Ids(ITs), env(Env), C))) ...</k>
         <env> Env </env>

    // Function
    rule <k> objDec(func I(ITs) : _ { E }) => obj(I |-> method(func(IdTypeExps2Ids(ITs), env(Env), E))) ...</k>
         <env> Env </env>

    // New
    context new HOLE
    rule <k> new class(I, N, SCD, env(Env')) => obj(.Map) ~> SCD ~> envE(Env, obj(This)) ...</k>
         <env> Env => Env'[I <- class(I, N, SCD, env(Env'))] </env>
         <this> This => .Map </this>

    // This
    rule <k> this => obj(This) ...</k>
         <this> This </this>

    // Dot
    rule <k> obj(M) . E => E ~> envEMethod(Env, obj(M)) ...</k>
         <env> Env => updateMap(Env, M) </env>

    // Method Procedure
    rule <k> methodProc(Is, env(Env'), C, O) ( Es ) ; => params(Is, Es) ~> setThis(O) ~> C ~> env(Env, obj(This)) ...</k>
         <env> Env => Env' </env>
         <this> This </this>
            requires isDvs(Es)

    // Method Function
    rule <k> methodFunc(Is, env(Env'), E, O) ( Es )
                => params(Is, Es) ~> setThis(O) ~> E ~> envE(Env, obj(This)) ...</k>
         <env> Env => Env' </env>
         <this> This </this>
            requires isDvs(Es)

    // Is Null
    syntax Exp ::= isNullF(Exp)
    context isNullF(HOLE)
    rule isNullF(E:Object) => isNull(E)
    rule <k> isNullF(L:Loc) => isNull(E) ...</k>
         <store>... L |-> E:Object ...</store>

    // Update default environment
    rule defaultEnvironment(List => List ListItem(2), Env => Env
        String2Id("isNull") |-> func(!E , .Ids, env(.Map), isNullF(!E)))
        requires notBool 2 in List

    // Auxilary Functions

    // used to set this
    syntax KItem ::= setThis(Object)
    rule <k> setThis(obj(This)) => . ...</k>
         <this> _ => This </this>

    // used to restore the environment, keeping the denotable value in front and supplying this for methods
    syntax KItem ::= envEMethod(Map, Object)
    rule method(proc(Is, Env', C)) ~> envEMethod(Env, O) => env(Env) ~> methodProc(Is, Env', C, O)
    rule method(func(Is, Env', E)) ~> envEMethod(Env, O) => env(Env) ~> methodFunc(Is, Env', E, O)
    rule E:Ev ~> envEMethod(Env, _) => env(Env) ~> E            [owise]
endmodule