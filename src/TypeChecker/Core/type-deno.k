requires "additional-syntax.k"
requires "../configuration.k"

module TYPE-DENO
    imports ADDITIONAL-SYNTAX
    imports CONFIGURATION

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
    context func ( _ ) HOLE
    rule func ( ITs:Types ) T => TFunc ITs T

    // File
    context file (HOLE => teval(HOLE))
    rule file T:Type => TFile T

    // Reference
    context (ref (HOLE => teval(HOLE))):TypeDeno
    rule (ref T:Type):TypeDeno => TRef T

    // Class
    rule <k> teval(I:Id => TObject N) ...</k>
         <tenv>... I |-> TClass N _ ...</tenv>

    // Type Infer
    context typeInfer(HOLE => reval(HOLE))
    rule typeInfer(T:Type) => T
endmodule