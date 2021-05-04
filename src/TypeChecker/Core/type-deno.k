requires "additional-syntax.k"

module TYPE-DENO
    imports ADDITIONAL-SYNTAX

    // Basic Types
    rule int => TInt
    rule float => TDouble
    rule bool => TBool
    rule string => TString

    // Array
    context array of HOLE
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
    context file HOLE
    rule file T:Type => TFile T

    // Reference
    context (ref HOLE):TypeDeno
    rule (ref T:Type):TypeDeno => TRef T

    // Type Infer
    context typeInfer(HOLE => reval(HOLE))
    rule typeInfer(T:Type) => T
endmodule