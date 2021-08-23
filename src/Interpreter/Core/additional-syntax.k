requires "../../Parser/small-syntax.k"
requires "../configuration.k"

module ADDITIONAL-SYNTAX
    imports SMALL-SYNTAX
    imports BOOL
    imports FLOAT
    imports MAP
    imports STRING
    imports ID
    imports CONFIGURATION
    imports MINT

    syntax Loc ::= Loc(Int)

    // Environments
    syntax Env ::= env(KItem)
                 | envE(KItem)
                 | emptyLocal()
    // Restore environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>
    rule <k> E:Ev ~> envE(Env) => E ...</k>
         <env> _ => Env </env>
    // Set local environment to empty
    rule <k> emptyLocal() => . ...</k>
         <localEnv> _ => .Map </localEnv>

    // Various types of values
    syntax Array ::= array(MInt{64}, MInt{64}, List)

    syntax Record ::= record(Map)

    syntax Proc ::= proc(Ids, Env, Com)
                  | recProc(Ids, Env, Com)
                  | methodProc(Ids, Env, Com, Object)

    syntax Func ::= func(Ids, Env, Exp)
                  | recFunc(Ids, Env, Exp)
                  | methodFunc(Ids, Env, Exp, Object)

    syntax File ::= file(List, Int, Loc)

    syntax Class ::= class(Id, Int, SCDec, Env)
                   | class(Id, Int, Class, SCDec, Env)

    syntax Object ::= obj(Map) | Null

    syntax Method ::= method(Proc)
                    | method(Func)

    // Command contiunuation
    syntax Cc ::= cc(K, Env)
    // Restore environment and run remaining
    rule cc(K, Env) => Env ~> K

    // Expression contiunuation
    syntax Ec ::= ec(K, Env)
    // Restore environment and run remaining using E
    rule E:Ev ~> ec(K, Env) => Env ~> E ~> K

    // Compound types
    syntax Rv ::= MInt{64} | Float | Bool | String | Loc | Array | Record | Object | Null

    syntax Sv ::= Rv | File                                     [owise]

    syntax Dv ::= Rv | Proc | Func | Class | Cc

    syntax Ev ::= Dv | Sv

    syntax Acc ::= Ev

    syntax KResult ::= Ev

    // Evaluate right-hand value
    syntax Acc ::= reval(Exp)
                 | #reval(Exp)                                  [strict]
    rule reval(E) => #reval(E)
        requires notBool isEv(E)                                [structural]
    rule #reval(E:Rv) => reval(E)
        requires notBool isLoc(E)                               [structural]
    rule <k> #reval(L) => reval(E) ...</k>
         <store>... L |-> E:Rv ...</store>

    // Used only for isDvs, checks all the Exp in Exps are Dvs
    syntax Dvs
    rule isDvs(E:Exp , Es:Exps) => true
        requires isDv(E) andBool isDvs(Es)
    rule isDvs(.Exps) => true
    rule isDvs(_) => false                                      [owise]

    // Used only for isEvs, checks all the Exp in Exps are Evs
    syntax Evs
    rule isEvs(E:Exp , Es:Exps) => true
        requires isEv(E) andBool isEvs(Es)
    rule isEvs(.Exps) => true
    rule isEvs(_) => false                                      [owise]

    // Updates the local environment
    syntax KItem ::= updateLocals(Ids, Exps)
                   | updateLocal(Id, Exp)
                   | updateLocalE(Id, Exp)
                   | updateLocal(Map)
    // Setup values to be assigned last to first
    rule updateLocals(I , Is, E , Es) => updateLocals(Is, Es) ~> updateLocal(I, E)  [structural]
    rule updateLocals(.Ids, .Exps) => .                         [structural]
    // Assign values to local environment
    rule <k> updateLocal(I, E) => . ...</k>
         <localEnv> Env => Env[I <- E] </localEnv>
    rule <k> E1:Ev ~> updateLocalE(I, E) => E1 ...</k>
         <localEnv> Env => Env[I <- E] </localEnv>
    // Update local environment with map
    rule <k> updateLocal(M) => . ...</k>
         <localEnv> Env => updateMap(Env, M) </localEnv>

    // Set return address
    syntax KItem ::= setReturn(Ec)
    rule <k> setReturn(Ec) => . ...</k>
         <return> _ => Ec </return>

    // Set this object
    syntax KItem ::= setThis(Object)
    rule <k> setThis(obj(This)) => . ...</k>
         <this> _ => This </this>
endmodule