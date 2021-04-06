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

    syntax Array ::= array(Int, Int, List)

    syntax Record ::= record(Map)

    syntax Proc ::= proc(Ids, Env, Com)
                  | recProc(Ids, Env, Com)

    syntax Func ::= func(Ids, Env, Exp)
                  | recFunc(Ids, Env, Exp)

    syntax File ::= file(List, Int, Loc)

    syntax Rv ::= Int | Float | Bool | String | Loc | Array | Record

    syntax Dv ::= Rv | Proc | Func | File

    syntax Dvs
    rule isDvs(E:Exp , Es:Exps) => true
        requires isDv(E) andBool isDvs(Es)
    rule isDvs(.Exps) => true
    rule isDvs(_) => false                                      [owise]

    syntax Exp ::= Dv

    syntax KResult ::= Dv

    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]

    syntax Pop ::= pop()
                 | popE()

    syntax Frame ::= frame(Int, Env, K)
endmodule