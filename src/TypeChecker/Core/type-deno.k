requires "additional-syntax.k"

module TYPE-DENO
    imports ADDITIONAL-SYNTAX

    // Eval type
    syntax TevalResult ::= Id | Type
    context teval(HOLE)                                         [result(TevalResult)]

    // Basic Types
    rule int => TInt
    rule float => TDouble
    rule bool => TBool
    rule string => TString

    // Array
    context array of (HOLE => teval(HOLE))
    rule array of T => TArray TRef T

    // Record
    context (record ( HOLE )):TypeExp                           [result(IdTypes)]
    rule (record ( ITs:IdTypes )):TypeExp => TRecord referAll(ITs)
        requires allDifferent(ids(ITs)) andBool referAll(ITs) =/=K ITError

    // Procedure
    context proc ( HOLE )                                       [result(Types)]
    rule proc ( ITs:Types ) => TProc ITs

    // Function
    context func ( HOLE ) _                                     [result(Types)]
    context func ( _ ) (HOLE => teval(HOLE))
    rule func ( ITs:Types ) T => TFunc ITs T

    // File
    context file (HOLE => teval(HOLE))
    rule file T:Type => TRef TFile T

    // Reference
    context (ref (HOLE => teval(HOLE))):TypeExp
    rule (ref T:Type):TypeExp => TRef T

    // Class
    rule <k> teval(I:Id => TObject N) ...</k>
         <tenv>... I |-> TClass N _ _ ...</tenv>

    // Type Infer
    context typeInfer(HOLE => reval(HOLE))
    rule typeInfer(T:Type) => T

    // TypeExps Conversion
    context ((HOLE => teval(HOLE)) , _):TypeExps
    context (_ , HOLE):TypeExps                                 [result(Types)]
    rule (T:Type , Ts:Types):TypeExps => T ,, Ts
    rule .TypeExps => .Types

    // IdTypeExps Conversion
    context _ : (HOLE => teval(HOLE)) , _
    context _ : _ , HOLE                                        [result(IdTypes)]
    rule I : T:Type , ITs:IdTypes => I : T ,, ITs
    rule .IdTypeExps => .IdTypes
endmodule