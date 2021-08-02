requires "type.k"
requires "../configuration.k"

module SUBTYPE
    imports TYPE
    imports CONFIGURATION

    // Subtype Relationship
    syntax Bool ::= Type "<=Type" Type                          [function, functional]
    // any cases
    rule TArray _ <=Type TArrayAny => true
    rule TRecord _ <=Type TRecordAny => true
    rule TProc _ <=Type TProcAny => true
    rule TFunc _ _ <=Type TFuncAny => true
    rule TFile _ <=Type TFileAny => true
    rule TRef _ <=Type TRefAny => true
    rule TClass _ _ _ <=Type TClassAny => true
    rule TObject _ <=Type TObjectAny => true
    rule TNull <=Type TObject _ => true
    rule TNull <=Type TObjectAny => true
    rule TUnion T1 ,, Ts1 <=Type TUnion T2 ,, Ts2
        => T1 <=Type TUnion Ts2 andBool
           TUnion Ts1 <=Type TUnion T2 ,, Ts2
    rule TUnion .Types <=Type TUnion _ => true
    rule T1 <=Type TUnion T2 ,, Ts
        => T1 <=Type T2 orBool
           T1 <=Type TUnion Ts                                  [priority(170)]
    rule _ <=Type TUnion .Types => false                        [priority(170)]
    // nested cases
    rule TArray T1 <=Type TArray T2 => T1 <=Type T2
    rule TRecord T1 <=Type TRecord T2 => allIn(T2, map(T1))
    rule TProc Ts1 <=Type TProc Ts2 => Ts2 <=Types Ts1
    rule TFunc Ts1 T1 <=Type TFunc Ts2 T2 => Ts2 <=Types Ts1 andBool T1 <=Type T2
    rule TFile T1 <=Type TFile T2 => T1 <=Type T2
    rule TRef T1 <=Type TRef T2 => T1 <=Type T2
    rule TRefMaybe T1 <=Type TRefMaybe T2 => T1 <=Type T2
    rule TObject N1 <=Type TObject N1 => true
    rule TObject _ <=Type TObject -1 => true                    [priority(160)]
    rule TObject -1 <=Type TObject _ => false                   [priority(170)]
    rule [[ TObject N1 <=Type TObject N2 => N12 ==Int N2 orBool TObject N12 <=Type TObject N2 ]]
         <classes>... N1 |-> TClass _ N12 _ ...</classes>       [priority(180)]
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