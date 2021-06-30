requires "additional-syntax.k"
requires "../configuration.k"
requires "../../Parser/double.k"
requires "../../Parser/altint.k"
requires "../helper.k"

module EXP
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION
    imports INTERPRETER-HELPER

    // Evaluate RVal
    rule reval(E) => #reval(E)
        requires notBool isEv(E)                                [structural]
    rule #reval(E:Rv) => reval(E)
        requires notBool isLoc(E)                               [structural]
    rule <k> #reval(L) => reval(E) ...</k>
         <store>... L |-> E:Rv ...</store>

    // Identifier
    rule <k> I:Id => E ...</k>
         <env>... I |-> E ...</env>

    // Read
    syntax KItem ::= #read(String)
    rule <k> read => #read("") ...</k>                          [structural]
    rule #read(S) => replaceAll(replaceAll(S, "\n", ""), "\r", "")
        requires countAllOccurrences(S, "\n") >Int 0
    rule <k> #read(S1) => #read(S1 +String S2) ...</k>
         <in> ListItem(S2:String) => .List ...</in>             [owise]

    // Array Expression
    context array [ HOLE => reval(HOLE) : _ ] : _               [result(Ev)]
    context array [ _:Ev : HOLE => reval(HOLE) ] : _            [result(Ev)]
    syntax KItem ::= createArrayLocs(Array, Int)
    rule array [ N1:MInt{64} : N2:MInt{64} ] : _ => createArrayLocs(array(N1, N2, .List), MInt2Signed(N2) -Int MInt2Signed(N1) +Int 1)
        requires N2 >=sMInt N1                                  [structural]
    rule <k> createArrayLocs(array(_, _, List => ListItem(Loc(!_N)) List), N => N -Int 1) ...</k>
        requires N >Int 0
    rule createArrayLocs(Array, 0) => Array

    // Record
    syntax KItem ::= createRecordLocs(Record, Ids)
    rule (record ( ITs )):Exp => createRecordLocs(record(.Map), IdTypeExps2Ids(ITs))   [structural]
    rule createRecordLocs(record(Map => Map[I <- Loc(!_N)]), (I , Is) => Is)
    rule createRecordLocs(Record, .Ids) => Record

    // Valof
    rule <k> valof : _ B ~> Rest => B ~> "No return encountered" </k>
         <env> Env => Env["return" <- !N] </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>

    // Function
    context HOLE:Exp ( _ )
    context _:Ev ( HOLE )                                       [result(Evs)]
    rule <k> func(Is, env(Env'), E) ( Es ) ~> Rest
                => params(Is, Es) ~> E ~> popE() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
            requires isEvs(Es)

    // Recursive Function
    rule recFunc(Is, Env, E) ( Es )
            => func(Is, Env, E) ( recFunc(Is, Env, E) , Es )    [structural]

    // Dot
    context (HOLE => reval(HOLE)) . _
    rule <k> record(REnv) . E ~> Rest => E ~> popE() </k>
         <env> Env => updateMap(Env, REnv) </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>

    // Array Access
    context (HOLE:Exp => reval(HOLE)) [ _ ]                     [result(Ev)]
    context _:Ev [ HOLE => reval(HOLE) ]                        [result(Ev)]
    rule array(N1, N2, List) [ N:MInt{64} ] => List[MInt2Signed(N -MInt N1)] requires N >=sMInt N1 andBool N <=sMInt N2

    // Contents
    context cont HOLE
    rule <k> cont L:Loc => E ...</k>
         <store>... L |-> E ...</store>

    // References Expression
    context ref HOLE:Exp
    rule <k> ref E:Ev => Loc(!N) ...</k>
         <store> Store => Store[Loc(!N) <- E] </store>

    // Not
    context ! (HOLE => reval(HOLE))
    rule ! B:Bool => notBool B

    // Positive
    context + (HOLE => reval(HOLE))
    rule + N:MInt{64} => N
    rule + N:Float => N

    // Negitive
    context - (HOLE => reval(HOLE))
    rule - N:MInt{64} => --MInt N
    rule - N:Float => --Float N

    // Ternary Operation (if then else)
    context (HOLE => reval(HOLE)) ? _ : _
    rule true ? E : _ => E
    rule false ? _ : E => E

    // Rules to turn a list of expressions into a list of denotable values
    context HOLE:Exp , _:Exps
    context _:Ev , HOLE:Exps
        requires HOLE =/=K .Exps                                [result(Evs)]
endmodule