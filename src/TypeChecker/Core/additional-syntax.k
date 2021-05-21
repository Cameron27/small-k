requires "../../Parser/small-syntax.k"
requires "../configuration.k"
requires "type.k"

module ADDITIONAL-SYNTAX
    imports SMALL-SYNTAX
    imports CONFIGURATION
    imports TYPE

    syntax Exp ::= Type
    syntax Exps ::= Types

    syntax KResult ::= Type

    syntax Exp ::= reval(Exp)
                 | #reval(Exp)                                  [strict]

    syntax TEnv ::= tenv(Map)
                  | tenvType(Map)
    // restore environment
    rule <k> tenv(TEnv) => . ...</k>
         <tenv> _ => TEnv </tenv>
    rule <k> T:Type ~> tenvType(TEnv) => T ...</k>
         <tenv> _ => TEnv </tenv>

    syntax KItem ::= returnType(Type)
    // set return type
    rule <k> returnType(T) => . ...</k>
         <returnType> _ => T </returnType>
endmodule