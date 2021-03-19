requires "small-syntax.k"
requires "configuration.k"

module HELPER
    imports SMALL-SYNTAX
    imports CONFIGURATION
    imports MAP

    syntax Loc ::= Loc(Int)

    syntax Env ::= env(Map)

    syntax Proc ::= proc(Id, Env, Com)

    syntax Func ::= func(Id, Env, Exp)

    syntax Rv ::= Int | Float | Bool | String

    syntax Dv ::= Loc | Rv | Proc | Func

    syntax Exp ::= Dv

    syntax KResult ::= Dv

    // Evaluate RVal
    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]
    rule reval(E) => #reval(E)
        requires notBool isDv(E)                                [structural]
    rule #reval(E) => reval(E)
        requires isRv(E)                                        [structural]
    rule <k> #reval(L) => reval(E) ...</k>
         <store>... L |-> E ...</store>

    // Restore Environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>
endmodule