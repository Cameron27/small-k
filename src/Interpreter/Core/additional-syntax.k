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

    syntax Env ::= env(Map)
                 | env(Map, Object)
    // restore environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>
    rule <k> env(Env, obj(This)) => . ...</k>
         <env> _ => Env </env>
         <this> _ => This </this>

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

    syntax Object ::= obj(ObjMap) | Null

    syntax Method ::= method(Proc)
                    | method(Func)

    syntax Rv ::= MInt{64} | Float | Bool | String | Loc | Array | Record | Object | Null

    syntax Ev ::= Rv | Proc | Func | Class | File

    syntax Exp ::= Ev

    syntax KResult ::= Ev

    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]

    // used only for isEvs, checks all the Exp in Exps are Evs
    syntax Evs
    rule isEvs(E:Exp , Es:Exps) => true
        requires isEv(E) andBool isEvs(Es)
    rule isEvs(.Exps) => true
    rule isEvs(_) => false                                      [owise]

    // used to pop the stack
    syntax KItem ::= pop()
    rule <k> pop() => Env ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>

    // used to pop the stack keeping the denotable value in front
    syntax KItem ::= popE()
    rule <k> E:Ev ~> popE() => Env ~> E ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>

    // used to store frame information
    syntax KItem ::= frame(Int, Env, K)

    // used to assign a list of parameters to a list of identifiers
    syntax KItem ::= params(Ids, Exps)
                   | param(Id, Exp)
    // setup params to be assigned last to first
    rule params(I , Is, E , Es) => params(Is, Es) ~> param(I, E)    [structural]
    rule params(.Ids, .Exps) => .                               [structural]
    // assign parameter to environment
    rule <k> param(I, E) => . ...</k>
         <env> Env => Env[I <- E] </env>
endmodule