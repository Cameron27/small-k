requires "small-syntax.k"
requires "configuration.k"
requires "operations.k"
requires "additional-syntax.k"

module SMALL
    imports SMALL-SYNTAX
    imports ADDITIONAL-SYNTAX
    imports LIST
    imports CONFIGURATION
    imports OPERATIONS

    // Evaluate RVal
    rule reval(E) => #reval(E)
        requires notBool isDv(E)                                [structural]
    rule #reval(E) => reval(E)
        requires isRv(E)                                        [structural]
    rule <k> #reval(L) => reval(E) ...</k>
         <store>... L |-> E ...</store>

    // Restore Environment
    rule <k> env(Env) => . ...</k>
         <env> _ => Env </env>

    // ---------------
    // |     Pgm     |
    // ---------------

    rule program C => C

    // ---------------
    // |     Exp     |
    // ---------------

    // Read
    syntax Read ::= #read(String)
    rule <k> read => #read("") ...</k>                          [structural]
    rule #read(S) => replaceAll(replaceAll(S, "\n", ""), "\r", "")
        requires countAllOccurrences(S, "\n") >Int 0
    rule <k> #read(S1) => #read(S1 +String S2) ...</k>
         <in> ListItem(S2:String) => .List ...</in>             [owise]

    // Identifier
    rule <k> I:Id => E ...</k>
         <env>... I |-> E ...</env>

    // Function
    syntax FuncClojure ::= funcClojure(Exp, Env)                [strict(1)]
    rule <k> func(I, env(Env'), E) ( E1:Dv )
                => funcClojure(E, env(Env)) ...</k>
         <env> Env => Env'[I <- E1] </env>
    rule funcClojure(E:Dv, Env) => Env ~> E                     [structural]

    // Ternary operation (if then else)
    context (HOLE => reval(HOLE)) ? _ : _
    rule true ? E : _ => E
    rule false ? _ : E => E

    // Operations in operations.k

    // ---------------
    // |     Com     |
    // ---------------

    // Assign
    context HOLE = _ ;
    context _:Loc = (HOLE => reval(HOLE)) ;
    rule <k> L:Loc = E:Rv ; => . ...</k>
         <store>... L |-> (_ => E) ...</store>

    // Output
    context output (HOLE => reval(HOLE)) ;
    rule <k> output E:Float ; => . ...</k>
         <out> List => List ListItem(printFloat(E)) ListItem("\n") </out>
    rule <k> output true ; => . ...</k>
         <out> List => List ListItem("true") ListItem("\n") </out>
    rule <k> output false ; => . ...</k>
         <out> List => List ListItem("false") ListItem("\n") </out>
    rule <k> output E:Rv ; => . ...</k>
         <out> List => List ListItem(E) ListItem("\n") </out>   [owise]

    // Procedure
    rule <k> proc(I, env(Env'), C) ( E:Dv ) ; => C ~> env(Env) ...</k>
         <env> Env => Env'[I <- E] </env>

    // If
    context if ( HOLE => reval(HOLE) ) _
    rule if ( true ) C => C
    rule if ( false ) _ => .
    context if ( HOLE => reval(HOLE) ) _ else _
    rule if ( true ) C else _ => C
    rule if ( false ) _ else C => C

    // While
    rule while (E) C => if (E) { .Decs C while (E) C }

    // Trap
    syntax Trap ::= trap(Env, K)
                  | trap(Int)
    syntax Escs ::= escs(Escs, Int)
    rule <k> trap { Ds Cs Escs } ~> Rest => escs(reverse(Escs), !N) ~> {Ds Cs} ~> trap(!N) </k>
         <env> Env </env>
         <traps> Traps => Traps[!N <- trap(env(Env), Rest)] </traps>    [structural]
    // add escape labels to the environment
    rule <k> escs((I:Id : Cs:Coms Escs:Escs => Escs), N) ...</k>
         <env> Env => Env[I <- cc(Cs, N)] </env>
    rule escs(.Escs, _) => .                                    [structural]
    // deal with either an escapeto or the whole trap body being run
    // TODO: if an inner trap escapesto an outer trap the inner trap is never cleared from memory
    rule <k> escapeto(cc(C, N)) ~> _ => Env ~> C ~> K </k>
         <traps>... N |-> trap(Env, K) => .Map ...</traps>      [structural]
    rule <k> trap(N) => Env ~> K </k>
         <traps>... N |-> trap(Env, K) => .Map ...</traps>      [structural]
    // reverse function for list of escapes so that first occurances will override later ones
    syntax Escs ::= reverse(Escs)                               [function]
                  | reverse(Escs, Escs)                         [function]
    rule reverse(X) => reverse(X, .Escs)
    rule reverse(X Xs, Ys) => reverse(Xs, X Ys)
    rule reverse(.Escs, Ys) => Ys

    // Escape
    syntax EscapeTo ::= escapeto(Cc)
    rule <k> escapeto I ; => escapeto(C) ...</k>
         <env>... I |-> C:Cc ...</env>

    // Block
    rule <k> { D:Decs C:Coms } => D ~> C ~> env(Env) ...</k>
         <env> Env </env>                                       [structural]

    rule C:Com Cs:Coms => C ~> Cs                               [structural]
    rule .Coms => .                                             [structural]

    // ---------------
    // |     Dec     |
    // ---------------

    // Constants
    context const _ = (HOLE => reval(HOLE)) ;
    rule <k> const I = E:Dv ; => . ...</k>
         <env> Env => Env[I <- E] </env>

    // Variables
    context var _ = (HOLE => reval(HOLE)) ;
    rule <k> var I = E:Rv ; => . ...</k>
         <env> Env => Env[I <- Loc(!L:Int)] </env>
         <store> Store => Store[Loc(!L) <- E] </store>

    // Procedure
    rule <k> proc I(I1) C => const I = proc(I1, env(Env), C) ; ...</k>
         <env> Env </env>                                       [structural]

    // Function
    rule <k> func I(I1) { E } => const I = func(I1, env(Env), E) ; ...</k>
         <env> Env </env>                                       [structural]

    rule D:Dec Ds:Decs => D ~> Ds                               [structural]
    rule .Decs => .                                             [structural]

    // ---------------
    // |    Other    |
    // ---------------

    // Handle exitcode
    rule <k> K </k>
         <exit-code> E => 1 </exit-code>
            requires E ==Int 0 andBool K =/=K .                 [priority(1000)]
endmodule