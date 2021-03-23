requires "small-syntax.k"

module ADDITIONAL-SYNTAX
    imports SMALL-SYNTAX
    imports BOOL
    imports FLOAT
    imports MAP
    imports STRING
    imports ID

    syntax Loc ::= Loc(Int)

    syntax Env ::= env(Map)

    syntax Proc ::= proc(Id, Env, Com)

    syntax Func ::= func(Id, Env, Exp)

    syntax Cc ::= cc(Coms, Int)

    syntax Rv ::= Int | Float | Bool | String

    syntax Dv ::= Loc | Rv | Proc | Func | Cc

    syntax Exp ::= Dv

    syntax KResult ::= Dv

    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]
endmodule