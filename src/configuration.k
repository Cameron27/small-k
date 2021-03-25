requires "small-syntax.k"

module CONFIGURATION
    imports SMALL-SYNTAX

    configuration <T>
        <env> .Map </env>
        <store> .Map </store>
        <stack> .List </stack>
        <in stream="stdin"> .List </in>
        <out stream="stdout"> .List </out>
        <exit-code exit=""> 0 </exit-code>
        <k> $PGM:Pgm </k>
    </T>
endmodule