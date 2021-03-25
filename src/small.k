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

    // Pop Stacks
    rule <k> E:Dv ~> popE() => Env ~> E ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>

    rule <k> pop() => Env ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>

    // Syntax for assigning parameters to values, used by procedures and functions
    syntax Params ::= params(Ids, Exps)
                    | param(Id, Exp)
    // setup params to be assigned last to first
    rule params(I , Is, E , Es) => params(Is, Es) ~> param(I, E)    [structural]
    rule params(.Ids, .Exps) => .                               [structural]
    // assign parameter to environment
    rule <k> param(I, E) => . ...</k>
         <env> Env => Env[I <- E] </env>

    // Rules to turn a list of expressions into a list of denotable values
    context HOLE:Exp , _:Exps
    context _:Dv , HOLE:Exps
        requires HOLE =/=K .Exps                                [result(Dvs)]

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
    context HOLE:Exp ( _ )
    context _:Dv ( HOLE )                                       [result(Dvs)]
    rule <k> func(Is, env(Env'), E) ( Es ) ~> Rest
                => params(Is, Es) ~> E ~> popE() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
            requires isDvs(Es)

    // Recursive Function
    rule recFunc(Is, Env, E) ( Es )
            => func(Is, Env, E) ( recFunc(Is, Env, E) , Es )    [structural]

    // Ternary operation (if then else)
    context (HOLE => reval(HOLE)) ? _ : _
    rule true ? E : _ => E
    rule false ? _ : E => E

    // Jumpout
    syntax Jump ::= jump(Int)
    syntax Dv ::= Jump
    // enter jumpout
    rule <k> jumpout I in E ~> Rest => E ~> popE() </k>
         <env> Env => Env[I <- jump(!N)] </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>
    // resolve incounted call of jump function
    rule <k> jump(N) ( E:Dv , .Exps ) ~> _ => Env ~> E ~> Rest </k>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> jump(N) ( _:Dv , .Exps ) ...</k>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M                                 [structural]

    // Valof
    // enter valof
    rule <k> valof B ~> Rest => B ~> "No return encountered" </k>
         <env> Env => Env["return" <- !N] </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>

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
    context HOLE ( _ ) ;
    context _:Dv ( HOLE ) ;                                     [result(Dvs)]
    // enter procedure
    rule <k> proc(Is, env(Env'), C) ( Es ) ; ~> Rest => params(Is, Es) ~> C ~> pop() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
            requires isDvs(Es)

    // Recursive Procedure
    rule recProc(Is, Env, C) ( Es ) ;
            => proc(Is, Env, C) ( recProc(Is, Env, C) , Es ) ;  [structural]

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
    syntax Escs ::= escs(Escs, Int)
                  | esc(Esc, Int)
    // enter trap
    rule <k> trap { Ds Cs Escs } ~> Rest => escs(Escs, !N) ~> { Ds Cs } ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!N, env(Env), Rest)) Stack </stack>
    // setup traps to be assigned last to first
    rule <k> escs((I : Cs Escs), N) => escs(Escs, N) ~> esc(I : Cs, N) ...</k>  [structural]
    rule escs(.Escs, _) => .                                    [structural]
    // add lables to environment
    syntax TrapLabel ::= trapLabel(Coms, Int)
    rule <k> esc(I : Cs, N) => . ...</k>
         <env> Env => Env[I <- trapLabel(Cs, N)] </env>
    // resolve an encountered escapeto
    rule <k> escapeto I ; ~> _ => Env ~> Cs ~> Rest </k>
         <env>... I |-> trapLabel(Cs, N) ...</env>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> escapeto I ;  ...</k>
         <env>... I |-> trapLabel(_, N) ...</env>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M                                 [structural]

    // Return
    context return (HOLE => reval(HOLE)) ;
    // resolve an encounted return
    rule <k> return E:Dv ; ~> _ => Env ~> E ~> Rest </k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(N, Env, Rest)) => .List ...</stack>
    // clear stack until correct stack frame is reached
    rule <k> return _:Dv ; ...</k>
         <env>... "return" |-> N ...</env>
         <stack> ListItem(frame(M, _, _)) => .List ...</stack>
            requires N =/=Int M

    // Block
    rule <k> { D:Decs C:Coms } ~> Rest => D ~> C ~> pop() </k>
         <env> Env </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>   [structural]

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
    rule <k> proc I(Is) C => const I = proc(Is, env(Env), C) ; ...</k>
         <env> Env </env>                                       [structural]

    // Recursive Procedure
    rule <k> rec proc I(Is) C => const I = recProc(I , Is, env(Env), C) ; ...</k>
         <env> Env </env>                                       [structural]

    // Function
    rule <k> func I(Is) { E } => const I = func(Is, env(Env), E) ; ...</k>
         <env> Env </env>                                       [structural]

    // Recursive Function
    rule <k> rec func I(Is) { E } => const I = recFunc(I , Is, env(Env), E) ; ...</k>
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