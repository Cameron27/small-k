requires "../../Common/helper.k"

module DEFAULT-ENVIRONMENT
    imports HELPER
    imports LIST
    imports MAP

    syntax Map ::= defaultEnvironment()                         [function]
                 | defaultEnvironment(List, Map)                [function]
    rule defaultEnvironment() => defaultEnvironment(.List, .Map)
    rule defaultEnvironment(_, Env) => Env                      [owise]
endmodule