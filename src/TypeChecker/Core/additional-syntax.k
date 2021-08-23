requires "../../Parser/small-syntax.k"
requires "../configuration.k"
requires "subtype.k"

module ADDITIONAL-SYNTAX
    imports SMALL-SYNTAX
    imports CONFIGURATION
    imports SUBTYPE

    syntax Acc ::= Type
    syntax Exps ::= Types

    syntax KResult ::= Type

    syntax Acc ::= reval(Exp)
                 | #reval(Exp)                                  [strict]

    // Evaluate type
    syntax TypeExp ::= teval(TypeExp)

    syntax TEnv ::= tenv(Map)
                  | tenvType(Map)
    // Restore environment
    rule <k> tenv(TEnv) => . ...</k>
         <tenv> _ => TEnv </tenv>
    rule <k> T:Type ~> tenvType(TEnv) => T ...</k>
         <tenv> _ => TEnv </tenv>

    // Set return type
    syntax KItem ::= setReturnType(Type)
    rule <k> setReturnType(T) => . ...</k>
         <returnType> _ => T </returnType>
endmodule