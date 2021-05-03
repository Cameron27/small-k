requires "../configuration.k"
requires "../Core/additional-syntax.k"

module FILES
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX

    // File
    rule <k> file F withbuffer B : _ ; => . ...</k>
         <env> Env => Env[B <- Loc(!B)][F <- Loc(!F)] </env>
         <store> Store => Store[Loc(!F) <- file(.List, 1, Loc(!B))] </store>
endmodule

module FILE-OPERATIONS
    imports CONFIGURATION
    imports ADDITIONAL-SYNTAX

    // Eof
    syntax Exp ::= eof(Exp)                                     [strict]
    rule <k> eof(L) => N >Int size(Es) ...</k>
         <store>... L |-> file(Es, N, _) ...</store>

    // File Commands
    // General framework for a file command
    syntax FileOpName ::= "resetf" | "rewritef" | "getf" | "putf"
    syntax FileOp ::= fileOp1(FileOpName, Exp)
                    | fileOp2(FileOpName, File, Loc)
                    | fileOp3(FileOpName, List, Int, BufferVal, Loc)
                    | fileRes(List, Int, BufferVal, Loc)
    syntax BufferVal ::= Dv | "unbound"
    context fileOp1(_, HOLE)
    rule <k> fileOp1(Op, FLoc) => fileOp2(Op, {Store[FLoc]}:>File, FLoc) ...</k>
         <store> Store </store>
            requires isFile(Store[FLoc])
    rule <k> fileOp2(Op, file(Es, N, L), FLoc) => fileOp3(Op, Es, N, {Store[L] orDefault unbound}:>BufferVal, FLoc) ...</k>
         <store> Store </store>
    rule <k> fileRes(Es, N, E:Dv, FLoc) => . ...</k>
         <store> Store => Store[FLoc <- file(Es, N, getBuffer(Store[FLoc]))][getBuffer(Store[FLoc]) <- E] </store>
    rule <k> fileRes(Es, N, unbound, FLoc) => . ...</k>
         <store> Store => Store[FLoc <- file(Es, N, getBuffer(Store[FLoc]))][getBuffer(Store[FLoc]) <- undef] </store>

    // Function to get the location buffer from a file
    syntax Loc ::= getBuffer(KItem)                             [function]
    rule getBuffer(file(_, _, L)) => L

    // Reset
    syntax Com ::= reset(Exp)
    rule reset(E) => fileOp1(resetf, E)
    rule fileOp3(resetf, Es, _, _, FLoc) => fileRes(Es, 1, {#if size(Es) >Int 0 #then Es[0] #else unbound #fi}:>BufferVal, FLoc)

    // Rewrite
    syntax Com ::= rewrite(Exp)
    rule rewrite(E) => fileOp1(rewritef, E)
    rule fileOp3(rewritef, _, _, _, FLoc) => fileRes(.List, 1, unbound, FLoc)

    // Get
    syntax Com ::= get(Exp)
    rule get(E) => fileOp1(getf, E)
    rule fileOp3(getf, Es, N, _, FLoc) => fileRes(Es, N +Int 1, {#if N ==Int size(Es) #then unbound #else Es[N] #fi}:>BufferVal, FLoc)
        requires N <=Int size(Es)

    // Put
    syntax Com ::= put(Exp)
    rule put(E) => fileOp1(putf, E)
    rule fileOp3(putf, Es, N, E:Dv, FLoc) => fileRes(Es ListItem(E), N +Int 1, unbound, FLoc)
        requires N ==Int size(Es) +Int 1
endmodule