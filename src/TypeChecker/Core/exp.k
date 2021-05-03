requires "../configuration.k"
requires "additional-syntax.k"

module EXP
    imports CONFIGURATION
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
    rule _:Int => TInt
    rule _:AltInt => TInt
    rule _:Double => TDouble
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
    context array [ _ : _ ] : HOLE
    rule array [ TInt : TInt ] : T => TArray refer(T)
        requires refer(T) =/=K TError

    // Record
    context (record ( HOLE )):Exp                               [result(IdTypes)]
    rule (record ( ITs )):Exp => TRecord referAll(ITs)
        requires allDifferent(ids(ITs)) andBool referAll(ITs) =/=K ITError

    // Valof
    context valof : HOLE _
    rule <k> valof : T:Type C => C ~> returnType(RT) ~> T ...</k>
         <returnType> RT => T </returnType>

    // Function
    context HOLE:Exp ( _:Exps )
    context _:Exp ( HOLE:Exps )                                 [result(Types)]
    rule TFunc Ts1 T ( Ts2 ) => T
        requires Ts1 ==Types Ts2

    // Dot
    context (HOLE => reval(HOLE)) . _
    rule <k> TRecord ITs . E => E ~> tenvType(TEnv) ...</k>
         <tenv> TEnv => updateMap(TEnv, map(ITs)) </tenv>

    // Array Access
    context (HOLE => reval(HOLE)):Exp [ _ ]                     [result(Type)]
    context _:Exp [ (HOLE => reval(HOLE)) ]                     [result(Type)]
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

    // Ternary (if then else)
    context (HOLE => reval(HOLE)) ? _ : _
    context _ ? HOLE : _
    context _ ? _ : HOLE
    rule TBool ? T1 : T2 => tryMerge(T1, T2)
        requires tryMerge(T1, T2) =/=K TError

    // Exps Conversion
    context (HOLE , _):Exps
    context (_ , HOLE):Exps                                     [result(Types)]
    rule (T , Ts):Exps => T ,, Ts                               [structural]
    rule .Exps => .Types                                        [structural]
endmodule