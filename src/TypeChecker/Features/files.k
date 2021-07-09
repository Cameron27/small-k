requires "../Core/additional-syntax.k"
requires "default-environment.k"

module FILES
    imports ADDITIONAL-SYNTAX
    imports DEFAULT-ENVIRONMENT
    imports ID

    // File
    context file _ withbuffer _ : (HOLE => teval(HOLE)) ;
    rule <k> file I1 withbuffer I2 : T ; => . ...</k>
         <tenv> TEnv => TEnv[I2 <- refer(T)][I1 <- refer(TFile T)] </tenv>
            requires refer(T) =/=K TError

    // Update default environment
    rule defaultEnvironment(List => List ListItem(1), Env => Env
        String2Id("reset") |-> TProc TRef TFileAny
        String2Id("rewrite") |-> TProc TRef TFileAny
        String2Id("get") |-> TProc TRef TFileAny
        String2Id("put") |-> TProc TRef TFileAny
        String2Id("eof") |-> TFunc TRef TFileAny TBool)
        requires notBool 1 in List
endmodule