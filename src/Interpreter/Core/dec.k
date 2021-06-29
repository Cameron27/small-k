requires "additional-syntax.k"
requires "../configuration.k"
requires "../Features/default-environment.k"
requires "../../Common/helper.k"
requires "../helper.k"

module DEC
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION
    imports DEFAULT-ENVIRONMENT
    imports K-LOCATIONS
    imports HELPER
    imports INTERPRETER-HELPER

    // Constant
    context const _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> const I : _ = E:Rv ; => . ...</k>
         <env> Env => Env[I <- E] </env>

    // Variable
    context var _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> var I : _ = E:Rv ; => . ...</k>
         <env> Env => Env[I <- Loc(!N)] </env>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Own
    syntax Dec ::= own(Id, FileLoc, Exp)
    syntax KItem ::= evalOwn(FileLoc, Exp)
    syntax FileLoc ::= fileLoc(Int, Int)
    // the location of the own declaration in the file is is used as the unique identifier for the declaration
    rule #location(own I : _ = E ;, _, SL, SC, _, _) => own(I, fileLoc(SL, SC), E)
    rule <k> own(I, FL, _) => . ...</k>
         <env> Env => Env[I <- L] </env>
         <globalEnv>... FL |-> L ...</globalEnv>                [owise]
    // first time evaluation, set exp to be evaluated and reset to default env
    rule <k> own(I, FL, E) ~> Rest => evalOwn(FL, E) ~> pop() </k>
         <env> Env => defaultEnvironment() </env>
         <globalEnv> GEnv </globalEnv>
         <stack> Stack => ListItem(frame(!_N, env(Env), own(I, FL, E) ~> Rest)) Stack </stack>
            requires notBool FL in_keys(GEnv)
    // eval the exp and create an binding in the global environment to a location
    context evalOwn(_, (HOLE => reval(HOLE)))
    rule <k> evalOwn(FL, E:Rv) => . ...</k>
         <globalEnv> GEnv => GEnv[FL <- Loc(!N)] </globalEnv>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Array
    context array _ [ HOLE => reval(HOLE) : _ ] : _ ;
    context array _ [ _:Dv : HOLE => reval(HOLE) ] : _ ;
    syntax KItem ::= createArrayLocs(Id, Array, Int)
    rule array I [ N1:MInt{64} : N2:MInt{64} ] : _ ; => createArrayLocs(I, array(N1, N2, .List), MInt2Signed(N2) -Int MInt2Signed(N1) +Int 1)
        requires N2 >=sMInt N1                                  [structural]
    rule createArrayLocs(_, array(_, _, List => ListItem(Loc(!_N)) List), N => N -Int 1)
        requires N >Int 0
    rule <k> createArrayLocs(I, Array, 0) => . ...</k>
         <env> Env => Env[I <- Array] </env>

    // Record
    syntax KItem ::= createRecordLocs(Id, Record, Ids)
    rule record I ( ITs ) ; => createRecordLocs(I, record(.Map), IdTypeDenos2Ids(ITs))  [structural]
    rule createRecordLocs(_, record(Map => Map[I <- Loc(!_N)]), (I , Is) => Is)
    rule <k> createRecordLocs(I, Record:Record, .Ids) => . ...</k>
         <env> Env => Env[I <- Record] </env>

    // Procedure
    rule <k> proc I(ITs) C => . ...</k>
         <env> Env => Env[I <- proc(IdTypeDenos2Ids(ITs), env(Env), C)] </env>  [structural]

    // Recursive Procedure
    rule <k> rec proc I(ITs) C => . ...</k>
         <env> Env => Env[I <- recProc(I , IdTypeDenos2Ids(ITs), env(Env), C)] </env>   [structural]

    // Function
    rule <k> func I(ITs) : _ { E } => . ...</k>
         <env> Env => Env[I <- func(IdTypeDenos2Ids(ITs), env(Env), E)] </env>  [structural]

    // Recursive Function
    rule <k> rec func I(ITs) : _ { E } => . ...</k>
         <env> Env => Env[I <- recFunc(I , IdTypeDenos2Ids(ITs), env(Env), E)] </env>   [structural]

    // Chain
    rule D1:Dec ; D2 => D1 ~> D2                                [structural]

    // Skip
    rule SkipDec => .
endmodule