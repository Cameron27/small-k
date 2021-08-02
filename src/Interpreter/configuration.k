requires "../Parser/small-syntax.k"

module CONFIGURATION
    imports SMALL-SYNTAX
    imports MAP

    configuration <T>
        <env> .Map </env>
        <globalEnv> .Map </globalEnv>
        <store> .Map </store>
        <this> .Map </this>
        <in stream="stdin"> .List </in>
        <out stream="stdout"> .List </out>
        <exit-code exit=""> 0 </exit-code>
        <k> $PGM:Pgm </k>
    </T>
endmodule