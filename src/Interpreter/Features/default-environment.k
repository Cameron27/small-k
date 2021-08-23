requires "../../Common/helper.k"

module DEFAULT-ENVIRONMENT
    imports HELPER
    imports LIST
    imports MAP

    syntax Map ::= defaultLocalEnvironment()                    [function]
                 | defaultLocalEnvironment(List, Map)           [function]
    rule defaultLocalEnvironment() => defaultLocalEnvironment(.List, .Map)
    rule defaultLocalEnvironment(_, Env) => Env                 [owise]
endmodule