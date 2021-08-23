requires "../Core/additional-syntax.k"
requires "default-environment.k"

module FILES
    imports ADDITIONAL-SYNTAX
    imports DEFAULT-ENVIRONMENT

    // File
    rule <k> file F withbuffer B : _ ; => . ...</k>
         <localEnv> Env => Env[B <- Loc(!B)][F <- Loc(!F)] </localEnv>
         <store> Store => Store[Loc(!F) <- file(.List, 1, Loc(!B))] </store>

    // Eof
    syntax Exp ::= eof(Exp)                                     [strict]
    rule <k> eof(L) => N >Int size(Es) ...</k>
         <store>... L |-> file(Es, N, _) ...</store>

    // File Commands
    // General framework for a file command
    syntax FileOpName ::= "resetf" | "rewritef" | "getf" | "putf"
    syntax FileState ::= fs(List, Int, BufferVal) // file values, windows location, buffer value
    syntax FileOp ::= fileOp1(FileOpName, Exp) // operation name, parameter expression
                    | fileOp2(FileOpName, File, Loc) // operation name, file, file location
                    | fileOp3(FileOpName, FileState, Loc, Loc) // operation name, file state, file location, buffer location
                    | fileRes(FileState, Loc, Loc) // new file state, file location, buffer location
    syntax BufferVal ::= Ev | "unbound"
    context fileOp1(_, HOLE)
    rule <k> fileOp1(Op, FLoc) => fileOp2(Op, File, FLoc) ...</k> // fileOp1 gets the file at the location
         <store>... FLoc |-> File ...</store>
    rule <k> fileOp2(Op, file(Es, N, BLoc), FLoc) => fileOp3(Op, fs(Es, N, {Store[BLoc] orDefault unbound}:>BufferVal), FLoc, BLoc) ...</k> // fileOp2 gets the file state as per the semantics
         <store> Store </store>
    rule <k> fileRes(fs(Es, N, E:Sv), FLoc, BLoc) => . ...</k> // fileRes updates file and buffer with new file state
         <store> Store => Store
                [FLoc <- file(Es, N, BLoc)]
                [getBuffer(Store[FLoc]) <- E] </store>
    rule <k> fileRes(fs(Es, N, unbound), FLoc, BLoc) => . ...</k>
         <store> Store => Store
            [FLoc <- file(Es, N, BLoc)]
            [BLoc <- undef] </store>

    // Function to get the location buffer from a file
    syntax Loc ::= getBuffer(KItem)                             [function]
    rule getBuffer(file(_, _, L)) => L

    // Reset
    syntax Com ::= reset(Exp)
    rule reset(E) => fileOp1(resetf, E)
    rule fileOp3(resetf, fs(Es, _, _), FLoc, BLoc) => fileRes(
            fs(Es, 1, {#if size(Es) >Int 0 #then Es[0] #else unbound #fi}:>BufferVal),
            FLoc, BLoc)

    // Rewrite
    syntax Com ::= rewrite(Exp)
    rule rewrite(E) => fileOp1(rewritef, E)
    rule fileOp3(rewritef, _, FLoc, BLoc) => fileRes(
        fs(.List, 1, unbound),
        FLoc, BLoc)

    // Get
    syntax Com ::= get(Exp)
    rule get(E) => fileOp1(getf, E)
    rule fileOp3(getf, fs(Es, N, _), FLoc, BLoc) => fileRes(
        fs(Es, N +Int 1, {#if N ==Int size(Es) #then unbound #else Es[N] #fi}:>BufferVal),
        FLoc, BLoc)
        requires N <=Int size(Es)

    // Put
    syntax Com ::= put(Exp)
    rule put(E) => fileOp1(putf, E)
    rule fileOp3(putf, fs(Es, N, E:Ev), FLoc, BLoc) => fileRes(
        fs(Es ListItem(E), N +Int 1, unbound),
        FLoc, BLoc)
        requires N ==Int size(Es) +Int 1

    // Update default environment
    rule defaultLocalEnvironment(List => List ListItem(1), Env => Env
        String2Id("reset") |-> proc(!E , .Ids, emptyLocal(), reset(!E))
        String2Id("rewrite") |-> proc(!E , .Ids, emptyLocal(), rewrite(!E))
        String2Id("get") |-> proc(!E , .Ids, emptyLocal(), get(!E))
        String2Id("put") |-> proc(!E , .Ids, emptyLocal(), put(!E))
        String2Id("eof") |-> func(!E , .Ids, emptyLocal(), eof(!E)))
        requires notBool 1 in List
endmodule