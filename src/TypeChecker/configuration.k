requires "../Parser/small-syntax.k"
requires "Core/type.k"

module CONFIGURATION
    imports SMALL-SYNTAX
    imports MAP
    imports TYPE

    configuration <T>
        <tenv> .Map </tenv>
        <returnType> TVoid </returnType>
        <classes> .Map </classes>
        <this> -1 </this>
        <exit-code exit=""> 0 </exit-code>
        <k> $PGM:Pgm </k>
    </T>
endmodule