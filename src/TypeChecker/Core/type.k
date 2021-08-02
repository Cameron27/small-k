requires "../../Parser/small-syntax.k"
requires "../../Common/helper.k"

module TYPE
    imports SMALL-SYNTAX
    imports K-EQUAL
    imports INT
    imports SET
    imports MAP
    imports HELPER

    syntax Type ::= "TInt"
                  | "TDouble"
                  | "TBool"
                  | "TString"
                  | "TArray" Type
                  | "TArrayAny"
                  | "TRecord" IdTypes
                  | "TRecordAny"
                  | "TProc" Types
                  | "TProcAny"
                  | "TFunc" Types Type
                  | "TFuncAny"
                  | "TFile" Type
                  | "TFileAny"
                  | "TRef" Type
                  | "TRefAny"
                  | "TRefMaybe" Type
                  | "TEscape"
                  | "TVoid"
                  | "TClass" Int Int Map
                  | "TClassAny"
                  | "TObject" Int
                  | "TObjectAny"
                  | "TNull"
                  | "TUnion" Types
                  | "TError"
    syntax Types ::= List{Type, ",,"}
    syntax IdType ::= Id ":" Type
    syntax IdTypes ::= List{IdType, ",,"}

    syntax TypeExp ::= Type
    syntax TypeExps ::= Types
    syntax IdTypeExps ::= IdTypes

    // Printable
    syntax Printable
    rule isPrintable(TInt) => true
    rule isPrintable(TDouble) => true
    rule isPrintable(TBool) => true
    rule isPrintable(TString) => true
    rule isPrintable(_) => false                                [owise]

    // Storable
    syntax Sv
    rule isSv(TInt) => true
    rule isSv(TDouble) => true
    rule isSv(TBool) => true
    rule isSv(TString) => true
    rule isSv(TRef _) => true
    rule isSv(TArray _) => true
    rule isSv(TRecord _) => true
    rule isSv(TFile _) => true
    rule isSv(TObject _) => true
    rule isSv(TNull) => true
    rule isSv(_) => false                                       [owise]

    // Right Hand
    syntax Rv
    rule isRv(TInt) => true
    rule isRv(TDouble) => true
    rule isRv(TBool) => true
    rule isRv(TString) => true
    rule isRv(TRef _) => true
    rule isRv(TArray _) => true
    rule isRv(TRecord _) => true
    rule isRv(TObject _) => true
    rule isRv(TNull) => true
    rule isRv(_) => false                                       [owise]

    // Reference
    syntax Type ::= refer(Type)                                 [function, functional]
    rule refer(T) => TRef T
        requires isSv(T)
    rule refer(_) => TError                                     [owise]

    // Reference All
    syntax IdTypes ::= referAll(IdTypes)                        [function, functional]
    rule referAll(I : T ,, ITs) => I : refer(T) ,, referAll(ITs)
        requires refer(T) =/=K TError andBool referAll(ITs) =/=K TError
    syntax IdTypes ::= "ITError"
    rule referAll(_) => ITError                                 [owise]
    rule referAll(.IdTypes) => .IdTypes

    // Ids from IdTypes
    syntax Ids ::= ids(IdTypes)                                 [function]
    rule ids(I : _ ,, ITs) => I , ids(ITs)
    rule ids(.IdTypes) => .Ids

    // Types from IdTypes
    syntax Types ::= types(IdTypes)                             [function]
    rule types(_ : T ,, ITs) => T ,, types(ITs)
    rule types(.IdTypes) => .Types

    // Maps from different Types
    syntax Map ::= map(IdTypes)                                 [function]
                 | map(Escs)                                    [function]
    rule map(I : T ,, ITs) => updateMap(map(ITs), I |-> T)
    rule map(.IdTypes) => .Map
    rule map(I : _ Escs) => updateMap(map(Escs), I |-> TEscape)
    rule map(.Escs) => .Map

    // Check all Ids are different
    syntax Bool ::= allDifferent(Ids)                           [function, functional]
    rule allDifferent(Is) => size(Is) ==Int size(idSet(Is))

    // Ids to Id Set
    syntax Set ::= idSet(Ids)                                   [function, functional]
    rule idSet(I , Is) => SetItem(I) idSet(Is)
    rule idSet(.Ids) => .Set

    // Size of Ids
    syntax Int ::= size(Ids)                                    [function, functional]
    rule size(_ , Is) => 1 +Int size(Is)
    rule size(.Ids) => 0
endmodule