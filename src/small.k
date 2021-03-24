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

    // Jumpout
    syntax Jump ::= jump(Id)
    syntax Dv ::= Jump
    // denotes the environment to be restored to and rest of the program for when the a jump is called
    syntax Jumpout ::= jumpout(Env, K)
    // used to identify end of jumpout was reached without a the jump being called and identify jumpouts in the environment
    syntax JumpoutId ::= jumpoutId(Id)
    rule <k> jumpout I in E ~> Rest => E ~> jumpoutId(I) </k> // calculate expression ending with a jumpoutId
         <env> Env => Env[I <- jump(I)][jumpoutId(I) <- jumpout(env(Env), Rest)] </env>
    // if the jump was never called restore the environment and pass the value to the rest of the program
    rule <k> E:Dv ~> jumpoutId(I) => Env ~> E ~> Rest </k>
         <env>... jumpoutId(I) |-> jumpout(Env, Rest) => .Map ...</env> [structural]
    // a jump call restores the environment and passes the value to the rest of the program
    rule <k> jump(I) ( E:Dv ) ~> _ => Env ~> E ~> Rest </k>
         <env>... jumpoutId(I) |-> jumpout(Env, Rest) => .Map ...</env>

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
    // denotes the environment to be restored to and rest of the program for when the trap is over or a escapeto is reached
    syntax Trap ::= trap(Env, K)
    // used to identify end of trap was reached without a escapeto and identify traps in the environment
    syntax TrapId ::= trapId(Int)
    syntax Escs ::= escs(Escs, Int)
    // setup escs to be added to env, run commands ending with a trapId
    rule <k> trap { Ds Cs Escs } ~> Rest => escs(reverse(Escs), !N) ~> {Ds Cs} ~> trapId(!N) </k>
         <env> Env => Env[trapId(!N) <- trap(env(Env), Rest)] </env>
    // add escape labels to the environment
    rule <k> escs((I:Id : Cs:Coms Escs:Escs => Escs), N) ...</k>
         <env> Env => Env[I <- cc(Cs, N)] </env>
    rule escs(.Escs, _) => .                                    [structural]
    // an escapeto restores the environment, run the escape commands then run the rest of the program
    rule <k> escapeto(cc(C, N)) ~> _ => Env ~> C ~> K </k>
         <env>... trapId(N) |-> trap(Env, K) ...</env>          [structural]
    // if no escapeto was hit then restore the environment and run the rest of the program
    rule <k> trapId(N) => Env ~> K </k>
         <env>... trapId(N) |-> trap(Env, K) ...</env>          [structural]
    // reverse function for list of escapes so that first occurances will override later ones
    syntax Escs ::= reverse(Escs)                               [function]
                  | reverse(Escs, Escs)                         [function]
    rule reverse(X) => reverse(X, .Escs)
    rule reverse(X Xs, Ys) => reverse(Xs, X Ys)
    rule reverse(.Escs, Ys) => Ys

    // Escape
    syntax EscapeTo ::= escapeto(Cc)
    rule <k> escapeto I ; => escapeto(C) ...</k>
         <env>... I |-> C:Cc ...</env> //TODO: Refactor this into the other part

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