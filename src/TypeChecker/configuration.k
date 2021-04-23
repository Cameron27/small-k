requires "../Parser/small-syntax.k"
requires "type.k"

module CONFIGURATION
    imports SMALL-SYNTAX
    imports MAP
    imports TYPE

    configuration <T>
        <tenv> .Map </tenv>
        <returnType> TVoid </returnType>
        <exit-code exit=""> 0 </exit-code>
        <k> $PGM:Pgm </k>
    </T>
endmodule