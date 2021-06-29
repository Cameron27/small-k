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
                  | "TClass" Int Map
                  | "TClassAny"
                  | "TObject" Int
                  | "TObjectAny"
                  | "TNull"
                  | "TMethod" Type
                  | "TMethodAny"
                  | "TUnion" Types
                  | "TError"
    syntax Types ::= List{Type, ",,"}
    syntax IdType ::= Id ":" Type
    syntax IdTypes ::= List{IdType, ",,"}

    syntax TypeExp ::= Type
    syntax TypeExps ::= Types
    syntax IdTypeExps ::= IdTypes

    // Subtype Relationship
    syntax Bool ::= Type "<=Type" Type                          [function, functional]
    // any cases
    rule TArray _ <=Type TArrayAny => true
    rule TRecord _ <=Type TRecordAny => true
    rule TProc _ <=Type TProcAny => true
    rule TFunc _ _ <=Type TFuncAny => true
    rule TFile _ <=Type TFileAny => true
    rule TRef _ <=Type TRefAny => true
    rule TClass _ _ <=Type TClassAny => true
    rule TObject _ <=Type TObjectAny => true
    rule TNull <=Type TObject _ => true
    rule TNull <=Type TObjectAny => true
    rule TMethod _ <=Type TMethodAny => true
    rule T1 <=Type TUnion T2 ,, Ts => T1 <=Type T2 orBool T1 <=Type TUnion Ts
    rule _ <=Type TUnion .Types => false
    // nested cases
    rule TArray T1 <=Type TArray T2 => T1 <=Type T2
    rule TRecord T1 <=Type TRecord T2 => allIn(T2, map(T1))
    rule TProc Ts1 <=Type TProc Ts2 => Ts2 <=Types Ts1
    rule TFunc Ts1 T1<=Type TFunc Ts2 T2 => Ts2 <=Types Ts1 andBool T1 <=Type T2
    rule TFile T1 <=Type TFile T2 => T1 <=Type T2
    rule TRef T1 <=Type TRef T2 => T1 <=Type T2
    rule TRefMaybe T1 <=Type TRefMaybe T2 => T1 <=Type T2
    rule TMethod T1 <=Type TMethod T2 => T1 <=Type T2
    rule T1 <=Type T2 => T1 ==K T2                              [owise]
    // Subtypes Relationship
    syntax Bool ::= Types "<=Types" Types                       [function, functional]
    rule T1 ,, Ts1 <=Types T2 ,, Ts2
        => T1 <=Type T2 andBool Ts1 <=Types Ts2
    rule .Types <=Types .Types => true
    rule _ <=Types _ => false                                   [owise]
    syntax Bool ::= Type "<=>Type" Type                         [function, functional]
    rule T1 <=>Type T2 => T1 <=Type T2 orBool T2 <=Type T1

    // Type Assignability
    syntax Bool ::= Type "assignable" Type                      [function, functional]
    rule T1 assignable T2 => TRef T1 <=Type T2

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

    // Try Merge
    syntax Type ::= tryMerge(Type, Type)                        [function, functional]
    rule tryMerge(TRef T1, TRef T2) => TRef tryMerge(T1, T2)    [priority(160)]
    rule tryMerge(TRefMaybe T1, TRefMaybe T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(160)]
    rule tryMerge(TRef T1, TRefMaybe T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(160)]
    rule tryMerge(TRefMaybe T1, TRef T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(160)]
    rule tryMerge(T1, TRefMaybe T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(180)]
    rule tryMerge(TRefMaybe T1, T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(180)]
    rule tryMerge(TRef T1, T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(180)]
    rule tryMerge(T1, TRef T2) => TRefMaybe maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(180)]
    rule tryMerge(T1, T2) => maxType(T1, T2)
        requires T1 <=>Type T2                                  [priority(190)]
    rule tryMerge(_, _) => TError                               [priority(200)]

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
    rule map(I :: _ Escs) => updateMap(map(Escs), I |-> TEscape)
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

    // Check all IdTypes are in the map from Ids to Types
    syntax Bool ::= allIn(IdTypes, Map)                         [function]
    rule allIn(I : T ,, ITs, M) => (T <=Type {M[I] orDefault TError}:>Type) andBool allIn(ITs, M)
    rule allIn(.IdTypes, _) => true

    // Gets the type that is the larger of the two
    syntax Type ::= maxType(Type, Type)                         [function, functional]
    rule maxType(T1, T2) => T1
        requires T2 <=Type T1
    rule maxType(T1, T2) => T2
        requires T1 <=Type T2
    rule maxType(_, _) => TError                                [owise]
endmodule