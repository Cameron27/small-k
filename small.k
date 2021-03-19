requires "helper.k"
requires "small-syntax.k"
requires "configuration.k"
requires "operations.k"

module SMALL
    imports SMALL-SYNTAX
    imports MAP
    imports LIST
    imports HELPER
    imports CONFIGURATION
    imports OPERATIONS

    // ---------------
    // |     Pgm     |
    // ---------------

    rule program C => C

    // ---------------
    // |     Exp     |
    // ---------------

    // Read
    syntax Read ::= read(String)
    rule <k> read => read("") ...</k>                           [structural]
    rule read(S) => replaceAll(replaceAll(S, "\n", ""), "\r", "")
        requires countAllOccurrences(S, "\n") >Int 0
    rule <k> read(S1) => read(S1 +String S2) ...</k>
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
    rule <k> output E:Rv ; => . ...</k>
         <out> List => List ListItem(E) ListItem("\n") </out>

    // Procedure
    rule <k> proc(I, env(Env'), C) ( E:Dv ) ; => C ~> env(Env) ...</k>
         <env> Env => Env'[I <- E] </env>

    // If
    context if ( HOLE => reval(HOLE) ) _ else _
    rule if ( true ) E else _ => E
    rule if ( false ) _ else E => E

    // While
    rule while (E) C => if (E) { C while (E) C} else {}

    // Block
    rule <k> { D:Dec C:Com } => D ~> C ~> env(Env) ...</k>
         <env> Env </env>                                       [structural]
    rule <k> { D:Dec } => D ~> env(Env)  ...</k>
         <env> Env </env>                                       [structural]
    rule { C:Com } => C                                         [structural]
    rule {  } => .                                              [structural]

    // Chain
    rule C1:Com C2:Com => C1 ~> C2                              [structural]

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

    // Chain
    rule D1:Dec D2:Dec => D1 ~> D2                              [structural]

    // ---------------
    // |    Other    |
    // ---------------

    // Handle exitcode
    rule <k> K </k>
         <exit-code> E => 1 </exit-code>
            requires E ==Int 0 andBool K =/=K .                 [priority(1000)]
endmodule