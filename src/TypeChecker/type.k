requires "../Parser/small-syntax.k"

module TYPE
    imports SMALL-SYNTAX
    imports K-EQUAL
    imports INT
    imports SET
    imports MAP

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
                  | "TError"
    syntax Types ::= List{Type, ",,"}
    syntax IdType ::= Id ":" Type
    syntax IdTypes ::= List{IdType, ",,"}

    syntax TypeDeno ::= Type

    // Type Equality
    syntax Bool ::= Type "==Type" Type                          [function, functional]
    rule TArray T1 ==Type TArray T2 => T1 ==Type T2
    rule TRecord T1 ==Type TRecord T2 => types(T1) ==Types types(T2)
    rule TProc Ts1 ==Type TProc Ts2 => Ts1 ==Types Ts2
    rule TFunc Ts1 T1 ==Type TFunc Ts2 T2 => Ts1 ==Types Ts2 andBool T1 ==Type T2
    rule TFile T1 ==Type TFile T2 => T1 ==Type T2
    rule TRef T1 ==Type TRef T2 => T1 ==Type T2
    rule TRefMaybe T1 ==Type TRefMaybe T2 => T1 ==Type T2
    rule TArray _ ==Type TArrayAny => true
    rule TArrayAny ==Type TArray _ => true
    rule TRecord _ ==Type TRecordAny => true
    rule TRecordAny ==Type TRecord _ => true
    rule TProc _ ==Type TProcAny => true
    rule TProcAny ==Type TProc _ => true
    rule TFunc _ _ ==Type TFuncAny => true
    rule TFuncAny ==Type TFunc _ _ => true
    rule TFile _ ==Type TFileAny => true
    rule TFileAny ==Type TFile _ => true
    rule TRef _ ==Type TRefAny => true
    rule TRefAny ==Type TRef _ => true
    rule T1 ==Type T2 => T1 ==K T2                              [owise]
    syntax Bool ::= Types "==Types" Types                       [function, functional]
    rule T1 ,, Ts1 ==Types T2 ,, Ts2
        => T1 ==Type T2 andBool Ts1 ==Types Ts2
    rule .Types ==Types .Types => true
    rule _ ==Types _ => false                                   [owise]

    // Type Assignability
    syntax Bool ::= Type "assignable" Type                      [function, functional]
    rule T1 assignable T2 => TRef T1 ==Type T2

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
    rule isRv(_) => false                                       [owise]

    // TypeDenos Conversion
    syntax TypeDenos ::= Types
    context (HOLE , _):TypeDenos
    context (_ , HOLE):TypeDenos                                [result(Types)]
    rule T:Type , Ts:Types => T ,, Ts
    rule .TypeDenos => .Types

    // IdTypeDenos Conversion
    syntax IdTypeDenos ::= IdTypes
    context _ : HOLE , _
    context _ : _ , HOLE                                        [result(IdTypes)]
    rule I : T:Type , ITs:IdTypes => I : T ,, ITs
    rule .IdTypeDenos => .IdTypes

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
    rule tryMerge(TRefMaybe T1, TRefMaybe T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(160)]
    rule tryMerge(TRef T1, TRefMaybe T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(160)]
    rule tryMerge(TRefMaybe T1, TRef T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(160)]
    rule tryMerge(T1, TRefMaybe T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(180)]
    rule tryMerge(TRefMaybe T1, T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(180)]
    rule tryMerge(TRef T1, T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(180)]
    rule tryMerge(T1, TRef T2) => TRefMaybe T1
        requires T1 ==K T2                                      [priority(180)]
    rule tryMerge(T1, T2) => T1
        requires T1 ==K T2                                      [priority(190)]
    rule tryMerge(_, _) => TError                               [priority(200)]


    // Ids From IdTypes
    syntax Ids ::= ids(IdTypes)                                 [function]
    rule ids(I : _ ,, ITs) => I , ids(ITs)
    rule ids(.IdTypes) => .Ids

    // Types From IdTypes
    syntax Types ::= types(IdTypes)                             [function]
    rule types(_ : T ,, ITs) => T ,, types(ITs)
    rule types(.IdTypes) => .Types

    // Maps From Different Types
    syntax Map ::= map(IdTypes)                                 [function]
                 | map(Escs)                                    [function, functional]
    rule map(I : T ,, ITs) => updateMap(map(ITs), I |-> T)
    rule map(.IdTypes) => .Map
    rule map(I : _ Escs) => updateMap(map(Escs), I |-> TEscape)
    rule map(.Escs) => .Map

    // Check All Ids Are Different
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