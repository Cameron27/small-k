requires "additional-syntax.k"

module EXP
    imports ADDITIONAL-SYNTAX

    // Evaluate RVal
    rule reval(E) => #reval(E)
        requires notBool isType(E)                              [structural]
    rule #reval(TRef T:Type) => reval(T)
        requires isRv(T)
    rule #reval(TRefMaybe T:Type) => reval(T)
        requires isRv(T)
    rule #reval(T) => reval(T)
        requires isRv(T)                                        [owise]

    // Basic Types
    rule _:MInt{64} => TInt
    rule _:Float => TDouble
    rule _:Bool => TBool
    rule _:String => TString

    // Identifier
    rule <k> I:Id => T ...</k>
         <tenv>... I |-> T ...</tenv>

    // Read
    rule read => TString

    // Array
    context array [ (HOLE => reval(HOLE)) : _ ] : _
    context array [ _ : (HOLE => reval(HOLE)) ] : _
    context array [ _ : _ ] : (HOLE => teval(HOLE))
    rule array [ TInt : TInt ] : T => TArray refer(T)
        requires refer(T) =/=K TError

    // Record
    context (record ( HOLE )):Exp                               [result(IdTypes)]
    rule (record ( ITs )):Exp => TRecord referAll(ITs)
        requires allDifferent(ids(ITs)) andBool referAll(ITs) =/=K ITError

    // Valof
    context valof : (HOLE => teval(HOLE)) _
    rule <k> valof : T:Type C => C ~> setReturnType(RT) ~> T ...</k>
         <returnType> RT => T </returnType>

    // Function
    context HOLE:Acc ( _:Exps )
    context _:Acc ( HOLE:Exps )                                 [result(Types)]
    rule TFunc Ts1 T ( Ts2 ) => T
        requires Ts2 <=Types Ts1

    // Dot
    context (HOLE => reval(HOLE)) . _
    rule <k> TRecord ITs . E => E ~> tenvType(TEnv) ...</k>
         <tenv> TEnv => updateMap(TEnv, map(ITs)) </tenv>

    // Array Access
    context (HOLE => reval(HOLE)):Acc [ _ ]                     [result(Type)]
    context _:Acc [ (HOLE => reval(HOLE)) ]                     [result(Type)]
    rule TArray T [ TInt ] => T

    // Content
    context cont HOLE
    rule cont TRef T => T

    // Reference
    context (ref HOLE):Exp
    rule (ref T):Exp => refer(T)
        requires refer(T) =/=K TError

    // Not
    context ! (HOLE => reval(HOLE))
    rule ! TBool => TBool

    // Positive
    context + (HOLE => reval(HOLE))
    rule + TInt => TInt
    rule + TFloat => TFloat

    // Negitive
    context - (HOLE => reval(HOLE))
    rule - TInt => TInt
    rule - TFloat => TFloat

    // Ternary (if then else)
    context (HOLE => reval(HOLE)) ? _ : _
    context _ ? HOLE : _
    context _ ? _ : HOLE
    rule TBool ? T1 : T2 => tryMerge(T1, T2)
        requires tryMerge(T1, T2) =/=K TError

    // Brackets
    rule brackets(E) => E

    // Exps Conversion
    context (HOLE , _):Exps
    context (_ , HOLE):Exps                                     [result(Types)]
    rule (T , Ts):Exps => T ,, Ts                               [structural]
    rule .Exps => .Types                                        [structural]
endmodule