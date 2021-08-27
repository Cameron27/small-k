requires "additional-syntax.k"
requires "../../Common/helper.k"
requires "../helper.k"

module DEC
    imports ADDITIONAL-SYNTAX
    imports HELPER
    imports INTERPRETER-HELPER

    // Constant
    context const _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> const I : _ = E:Rv ; => . ...</k>
         <localEnv> Env => Env[I <- E] </localEnv>

    // Variable
    context var _ : _ = (HOLE => reval(HOLE)) ;
    rule <k> var I : _ = E:Rv ; => . ...</k>
         <localEnv> Env => Env[I <- Loc(!N)] </localEnv>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Array
    context array _ [ HOLE => reval(HOLE) : _ ] : _ ;
    context array _ [ _:Ev : HOLE => reval(HOLE) ] : _ ;
    syntax KItem ::= createArrayLocs(Id, Array, Int)
    rule array I [ N1:MInt{64} : N2:MInt{64} ] : _ ; => createArrayLocs(I, array(N1, N2, .List), MInt2Signed(N2) -Int MInt2Signed(N1) +Int 1)
        requires N2 >=sMInt N1                                  [structural]
    rule createArrayLocs(_, array(_, _, List => ListItem(Loc(!_N)) List), N => N -Int 1)
        requires N >Int 0
    rule <k> createArrayLocs(I, Array, 0) => . ...</k>
         <localEnv> Env => Env[I <- Array] </localEnv>

    // Record
    syntax KItem ::= createRecordLocs(Id, Record, Ids)
    rule record I ( ITs ) ; => createRecordLocs(I, record(.Map), IdTypeExps2Ids(ITs))   [structural]
    rule createRecordLocs(_, record(Map => Map[I <- Loc(!_N)]), (I , Is) => Is)
    rule <k> createRecordLocs(I, Record:Record, .Ids) => . ...</k>
         <localEnv> Env => Env[I <- Record] </localEnv>

    // Procedure
    rule <k> proc I(ITs) C => updateLocal(I, proc(IdTypeExps2Ids(ITs), env(<env> Env </env>), C)) ...</k>
         <env> Env </env>

    // Recursive Procedure
    rule <k> rec proc I(ITs) C => updateLocal(I, recProc(I , IdTypeExps2Ids(ITs), env(<env> Env </env>), C)) ...</k>
         <env> Env </env>

    // Function
    rule <k> func I(ITs) : _ { E } => updateLocal(I, func(IdTypeExps2Ids(ITs), env(<env> Env </env>), E)) ...</k>
         <env> Env </env>

    // Recursive Function
    rule <k> rec func I(ITs) : _ { E } => updateLocal(I, recFunc(I , IdTypeExps2Ids(ITs), env(<env> Env </env>), E)) ...</k>
         <env> Env </env>

    // Chain
    rule D1:Dec D2 => D1 ~> D2                                  [structural]

    // Skip
    rule SkipDec => .
endmodule