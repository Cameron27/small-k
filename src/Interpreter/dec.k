requires "additional-syntax.k"
requires "configuration.k"
requires "default-environment.k"

module DEC
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION
    imports DEFAULT-ENVIRONMENT
    imports K-LOCATIONS

    // Constants
    context const _ = (HOLE => reval(HOLE)) ;
    rule <k> const I = E:Rv ; => . ...</k>
         <env> Env => Env[I <- E] </env>

    // Variables
    context var _ = (HOLE => reval(HOLE)) ;
    rule <k> var I = E:Rv ; => . ...</k>
         <env> Env => Env[I <- Loc(!N)] </env>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Own
    syntax Dec ::= own(Id, FileLoc, Exp)
    syntax KItem ::= evalOwn(FileLoc, Exp)
    syntax FileLoc ::= fileLoc(Int, Int)
    // the location of the own declaration in the file is is used as the unique identifier for the declaration
    rule #location(own I = E ;, _, SL, SC, _, _) => own(I, fileLoc(SL, SC), E)
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
    context array _ [ HOLE => reval(HOLE) : _ ] ;
    context array _ [ _:Dv : HOLE => reval(HOLE) ] ;
    syntax KItem ::= createArrayLocs(Id, Array, Int)
    rule array I [ N1:Int : N2:Int ] ; => createArrayLocs(I, array(N1, N2, .List), N2 -Int N1 +Int 1)
        requires N2 >=Int N1                                    [structural]
    rule <k> createArrayLocs(_, array(_, _, List => ListItem(Loc(!_N)) List), N => N -Int 1) ...</k>
        requires N >Int 0
    rule <k> createArrayLocs(I, Array, 0) => . ...</k>
         <env> Env => Env[I <- Array] </env>

    // Record
    syntax KItem ::= createRecordLocs(Id, Record, Ids)
    rule record I ( Is ) ; => createRecordLocs(I, record(.Map), Is) [structural]
    rule createRecordLocs(_, record(Map => Map[I <- Loc(!_N)]), (I , Is) => Is)
    rule <k> createRecordLocs(I, Record:Record, .Ids) => . ...</k>
         <env> Env => Env[I <- Record] </env>

    // File
    rule <k> file F withbuffer B ; => . ...</k>
         <env> Env => Env[B <- Loc(!B)][F <- Loc(!F)] </env>
         <store> Store => Store[Loc(!F) <- file(.List, 1, Loc(!B))] </store>

    // Procedure
    rule <k> proc I(Is) C => . ...</k>
         <env> Env => Env[I <- proc(Is, env(Env), C)] </env>    [structural]

    // Recursive Procedure
    rule <k> rec proc I(Is) C => . ...</k>
         <env> Env => Env[I <- recProc(I , Is, env(Env), C)] </env> [structural]

    // Function
    rule <k> func I(Is) { E } => . ...</k>
         <env> Env => Env[I <- func(Is, env(Env), E)] </env>    [structural]

    // Recursive Function
    rule <k> rec func I(Is) { E } => . ...</k>
         <env> Env => Env[I <- recFunc(I , Is, env(Env), E)] </env> [structural]

    rule D:Dec Ds:Decs => D ~> Ds                               [structural]
    rule .Decs => .                                             [structural]
endmodule