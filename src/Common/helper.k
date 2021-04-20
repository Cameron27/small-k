module HELPER
    imports INT
    imports FLOAT
    imports STRING

    // Float to string
    syntax String ::= printFloat(Float)                         [function]
                    | printFloat(String)                        [function]
                    | printFloatNeg(String)                     [function]
                    | printFloat(String, Int)                   [function]
                    | printFloat(String, String)                [function]
    rule printFloat(F) => printFloat(Float2String(F)) // convert to string

    rule printFloat(S) => printFloatNeg(printFloat(dropString(S, 1)))
        requires headString(S) ==String "-"

    rule printFloat(S) => printFloat(substrString(S, 0, findString(S, "e", 0)), // remove exponental
                                        String2Int(dropString(S, findString(S, "e", 0) +Int 1)))    [owise] // get exponential as int

    rule printFloatNeg(S) => "-" +String S

    rule printFloat(S, I) => printFloat(substrString(S, 2, 2 +Int I), dropString(S, 2 +Int I)) // split based on where '.' goes
        requires I >Int 0 andBool 2 +Int I <Int lengthString(S)
    rule printFloat(S, I) => printFloat(dropString(S, 2) +String
                                                stringMult("0", I -Int lengthString(S) +Int 2),
                                            "0") // string is shorter then whole number part so pad with 0
        requires I >Int 0 andBool 2 +Int I >=Int lengthString(S)
    rule printFloat(S, I) => printFloat("0", stringMult("0", 0 -Int I) +String dropString(S, 2)) // no whole nuber part so just pad with 0
        requires I <=Int 0

    rule printFloat(S1, S2) =>
        S1 +String "." +String trimEnd(S2, "0") // join with '.'
            requires String2Int(S2) >Int 0
    rule printFloat(S1, S2) => S1 +String ".0" // just whole number part as there is no decimal
        requires String2Int(S2) ==Int 0

    // Multiply a string i.e. stringMult("a", 5) = "aaaaa"
    syntax String ::= stringMult(String, Int)                   [function, functional]
                    | stringMult(String, Int, String)           [function, functional]
    rule stringMult(S, I) => stringMult(S, I, "")
    rule stringMult(_, I, O) => O
        requires I <=Int 0
    rule stringMult(S, I, O) => stringMult(S, I -Int 1, O +String S)
        requires I >Int 0

    // Trim certain characters from end of string
    syntax String ::= trimEnd(String, String)                   [function, functional]
    rule trimEnd(S, Cs) => trimEnd(substrString(S, 0, lengthString(S) -Int 1), Cs)
        requires lengthString(S) >Int 0 andBool
            lengthString(S) -Int 1 ==Int rfindChar(S, Cs, lengthString(S) -Int 1)
    rule trimEnd(S, _) => S                                     [owise]

    // Drop first n characters from a string
    syntax String ::= dropString(String, Int)                   [function, functional]
    rule dropString(S, I) => substrString(S, I, lengthString(S))

    // Get the first character from a string
    syntax String ::= headString(String)                        [function, functional]
    rule headString(S) => substrString(S, 0, 1)

    syntax Int ::= sign(Int)                                    [function, functional]
    rule sign(X) => 1
        requires X >Int 0
    rule sign(X) => 0
        requires X ==Int 0
    rule sign(X) => -1
        requires X <Int 0
endmodule