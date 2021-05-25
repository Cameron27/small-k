requires "../configuration.k"
requires "../Core/additional-syntax.k"
requires "../helper.k"

module CLASSES
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX
    imports INTERPRETER-HELPER

    // Class
    rule <k> class I SCD => . ...</k>
         <env> Env => Env[I <- class(I, !_, SCD, env(Env["return" <- undef]))] </env>

    // New
    context new HOLE
    rule <k> new class(I, N, SCD, env(Env')) ~> Rest => SCD ~> getThis() ~> popE() </k>
         <env> Env => Env'[I <- class(I, N, SCD, env(Env'))] </env>
         <stack> Stack => ListItem(frame(!_, env(Env, obj(This)), Rest)) Stack </stack>
         <this> This => N, .Map, .Map </this>

    syntax KItem ::= objDec(Dec)
                   | "public"
                   | "private"
    rule public D => objDec(D) ~> public
    rule <k> M:Map ~> public => . ...</k>
         <this> _, (Obj => updateMap(Obj, M)), _ </this>
    rule <k> M:Map ~> private => . ...</k>
         <this> _, _, (Obj => updateMap(Obj, M)) </this>
    rule private D => objDec(D) ~> private

    // Chain
    rule SCD1:SCDec ; SCD2 => SCD1 ~> SCD2                      [structural]

    // Skip
    rule SkipSCDec => .

    // Constant
    context objDec(const _ : _ = (HOLE => reval(HOLE)) ;)
    rule objDec(const I : _ = E:Rv ;) => I |-> E

    // Variable
    context objDec(var _ : _ = (HOLE => reval(HOLE)) ;)
    rule <k> objDec(var I : _ = E:Rv ;) => I |-> Loc(!N) ...</k>
         <store> Store => Store[Loc(!N) <- E] </store>

    // // File
    rule <k> objDec(file F withbuffer B : _ ;) => updateMap(B |-> Loc(!B), F |-> Loc(!F)) ...</k>
         <store> Store => Store[Loc(!F) <- file(.List, 1, Loc(!B))] </store>

    // Procedure
    rule <k> objDec(proc I(ITs) C) => I |-> method(proc(IdTypeDenos2Ids(ITs), env(Env), C)) ...</k>
         <env> Env </env>

    // Function
    rule <k> objDec(func I(ITs) : _ { E }) => I |-> method(func(IdTypeDenos2Ids(ITs), env(Env), E)) ...</k>
         <env> Env </env>

    // This
    rule <k> this => obj(This) ...</k>
         <this> This </this>

    // Dot
    rule <k> obj(N1, Public , Private) . E ~> Rest => E ~> popEMethod(obj(N1, Public , Private)) </k>
         <env> Env => #if N1 ==Int N2 #then updateMap(updateMap(Env, Public), Private) #else updateMap(Env, Public) #fi </env>
         <stack> Stack => ListItem(frame(!_N, env(Env), Rest)) Stack </stack>
         <this> N2, _, _ </this>

    // Method Procedure
    rule <k> methodProc(Is, env(Env'), C, O) ( Es ) ; ~> Rest => params(Is, Es) ~> setThis(O) ~> C ~> pop() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env, obj(This)), Rest)) Stack </stack>
         <this> This </this>
            requires isDvs(Es)

    // Method Function
    rule <k> methodFunc(Is, env(Env'), E, O) ( Es ) ~> Rest
                => params(Is, Es) ~> setThis(O) ~> E ~> popE() </k>
         <env> Env => Env' </env>
         <stack> Stack => ListItem(frame(!_N, env(Env, obj(This)), Rest)) Stack </stack>
         <this> This </this>
            requires isDvs(Es)

    // Auxilary Functions

    // used to set this
    syntax KItem ::= setThis(Object)
    rule <k> setThis(obj(This)) => . ...</k>
         <this> _ => This </this>

    // used to get this
    syntax KItem ::= getThis()
    rule <k> getThis() => obj(This) ...</k>
         <this> This </this>

    // used to pop the stack keeping the denotable value in front and supplying this for methods
    syntax KItem ::= popEMethod(Object)
    rule <k> method(proc(Is, Env', C)) ~> popEMethod(O) => Env ~> methodProc(Is, Env', C, O) ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>
    rule <k> method(func(Is, Env', E)) ~> popEMethod(O) => Env ~> methodFunc(Is, Env', E, O) ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack>
    rule <k> E:Dv ~> popEMethod(_) => Env ~> E ~> Rest </k>
         <stack> ListItem(frame(_, Env, Rest)) => .List ...</stack> [owise]
endmodule

module CLASS-OPERATIONS
    imports ADDITIONAL-SYNTAX

    syntax Exp ::= isNullF(Exp)
    context isNullF(HOLE)
    rule isNullF(E:Object) => isNull(E)
    rule <k> isNullF(L:Loc) => isNull(E) ...</k>
         <store>... L |-> E:Object ...</store>
endmodule