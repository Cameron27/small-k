requires "small-syntax.k"

module CONFIGURATION
    imports SMALL-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
        <env> .Map </env>
        <store> .Map </store>
        <conts> .Map </conts>
        <in stream="stdin"> .List </in>
        <out stream="stdout"> .List </out>
        <exit-code exit=""> 0 </exit-code>
    </T>
endmodule