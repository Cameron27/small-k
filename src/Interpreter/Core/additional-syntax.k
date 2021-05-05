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
    // restore environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>

    syntax Array ::= array(MInt{64}, MInt{64}, List)

    syntax Record ::= record(Map)

    syntax Proc ::= proc(Ids, Env, Com)
                  | recProc(Ids, Env, Com)

    syntax Func ::= func(Ids, Env, Exp)
                  | recFunc(Ids, Env, Exp)

    syntax File ::= file(List, Int, Loc)

    syntax Rv ::= MInt{64} | Float | Bool | String | Loc | Array | Record

    syntax Dv ::= Rv | Proc | Func | File

    syntax Exp ::= Dv

    syntax KResult ::= Dv

    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]

    // used only for isDvs, checks all the Exp in Exps are Dvs
    syntax Dvs
    rule isDvs(E:Exp , Es:Exps) => true
        requires isDv(E) andBool isDvs(Es)
    rule isDvs(.Exps) => true
    rule isDvs(_) => false                                      [owise]

    syntax KItem ::= pop()
                   | popE()
    // used to pop the stack
    rule <k> pop() => Env ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>
    rule <k> E:Dv ~> popE() => Env ~> E ~> Rest </k>
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