requires "../Parser/small-syntax.k"

module CONFIGURATION
    imports SMALL-SYNTAX
    imports MAP

    syntax Ec ::= "no return"
    configuration <T>
        <env>
            <localEnv> .Map </localEnv>
            <globalEnv> .Map </globalEnv>
            <return> no return </return>
            <this> .Map </this>
        </env>
        <store> .Map </store>
        <in stream="stdin"> .List </in>
        <out stream="stdout"> .List </out>
        <exit-code exit=""> 0 </exit-code>
        <k> $PGM:Pgm </k>
    </T>
endmodule