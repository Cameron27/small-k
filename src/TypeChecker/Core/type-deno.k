requires "additional-syntax.k"
requires "../configuration.k"

module TYPE-DENO
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION

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
    context (record ( HOLE )):TypeDeno                          [result(IdTypes)]
    rule (record ( ITs:IdTypes )):TypeDeno => TRecord referAll(ITs)
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
    context (ref (HOLE => teval(HOLE))):TypeDeno
    rule (ref T:Type):TypeDeno => TRef T

    // Class
    rule <k> teval(I:Id => TObject N) ...</k>
         <tenv>... I |-> TClass N _ ...</tenv>

    // Type Infer
    context typeInfer(HOLE => reval(HOLE))
    rule typeInfer(T:Type) => T

    // TypeDenos Conversion
    context ((HOLE => teval(HOLE)) , _):TypeDenos
    context (_ , HOLE):TypeDenos                                [result(Types)]
    rule (T:Type , Ts:Types):TypeDenos => T ,, Ts
    rule .TypeDenos => .Types

    // IdTypeDenos Conversion
    context _ : (HOLE => teval(HOLE)) , _
    context _ : _ , HOLE                                        [result(IdTypes)]
    rule I : T:Type , ITs:IdTypes => I : T ,, ITs
    rule .IdTypeDenos => .IdTypes
endmodule