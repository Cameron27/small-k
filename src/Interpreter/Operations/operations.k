requires "../additional-syntax.k"

module OPERATIONS
    imports ADDITIONAL-SYNTAX
    imports FLOAT

    context (HOLE => reval(HOLE)) * _                           [result(Rv)]
    context E * (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) / _                           [result(Rv)]
    context E / (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) % _                           [result(Rv)]
    context E % (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) + _                           [result(Rv)]
    context E + (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) - _                           [result(Rv)]
    context E - (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) < _                           [result(Rv)]
    context E < (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) <= _                          [result(Rv)]
    context E <= (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) > _                           [result(Rv)]
    context E > (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) >= _                          [result(Rv)]
    context E >= (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) == _                          [result(Rv)]
    context E == (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) != _                          [result(Rv)]
    context E != (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) & _                           [result(Rv)]
    context E & (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) ^ _                           [result(Rv)]
    context E ^ (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]
    context (HOLE => reval(HOLE)) | _                           [result(Rv)]
    context E | (HOLE => reval(HOLE))
        requires isRv(E)                                        [result(Rv)]


    rule E1:Int		*	E2:Int		=>	E1						*Int		E2
    rule E1:Float	*	E2:Float	=>	E1						*Float		E2
    rule E1:Int		*	E2:Float	=>	Int2Float(E1, 53, 11)	*Float		E2
    rule E1:Float	*	E2:Int		=>	E1						*Float		Int2Float(E2, 53, 11)
    rule E1:Int		/	E2:Int		=>	E1						/Int		E2
        requires E2 =/=Int 0
    rule E1:Float	/	E2:Float	=>	E1						/Float		E2
        requires E2 =/=Float 0d
    rule E1:Int		/	E2:Float	=>	Int2Float(E1, 53, 11)	/Float		E2
        requires E2 =/=Float 0d
    rule E1:Float	/	E2:Int		=>	E1						/Float		Int2Float(E2, 53, 11)
        requires E2 =/=Int 0
    rule E1:Int		%	E2:Int		=>	E1						%Int		E2
        requires E2 =/=Int 0
    rule E1:Int		+	E2:Int		=>	E1						+Int		E2
    rule E1:Float	+	E2:Float	=>	E1						+Float		E2
    rule E1:Int		+	E2:Float	=>	Int2Float(E1, 53, 11)	+Float		E2
    rule E1:Float	+	E2:Int		=>	E1						+Float		Int2Float(E2, 53, 11)
    rule E1:String	+	E2:String	=>	E1						+String		E2
    rule E1:Int		-	E2:Int		=>	E1						-Int		E2
    rule E1:Float	-	E2:Float	=>	E1						-Float		E2
    rule E1:Int		-	E2:Float	=>	Int2Float(E1, 53, 11)	-Float		E2
    rule E1:Float	-	E2:Int		=>	E1						-Float		Int2Float(E2, 53, 11)
    rule E1:Int		<	E2:Int		=>	E1						<Int		E2
    rule E1:Float	<	E2:Float	=>	E1						<Float		E2
    rule E1:Int		<	E2:Float	=>	Int2Float(E1, 53, 11)	<Float		E2
    rule E1:Float	<	E2:Int		=>	E1						<Float		Int2Float(E2, 53, 11)
    rule E1:Int		<=	E2:Int		=>	E1						<=Int		E2
    rule E1:Float	<=	E2:Float	=>	E1						<=Float		E2
    rule E1:Int		<=	E2:Float	=>	Int2Float(E1, 53, 11)	<=Float		E2
    rule E1:Float	<=	E2:Int		=>	E1						<=Float		Int2Float(E2, 53, 11)
    rule E1:Int		>	E2:Int		=>	E1						>Int		E2
    rule E1:Float	>	E2:Float	=>	E1						>Float		E2
    rule E1:Int		>	E2:Float	=>	Int2Float(E1, 53, 11)	>Float		E2
    rule E1:Float	>	E2:Int		=>	E1						>Float		Int2Float(E2, 53, 11)
    rule E1:Int		>=	E2:Int		=>	E1						>=Int		E2
    rule E1:Float	>=	E2:Float	=>	E1						>=Float		E2
    rule E1:Int		>=	E2:Float	=>	Int2Float(E1, 53, 11)	>=Float		E2
    rule E1:Float	>=	E2:Int		=>	E1						>=Float		Int2Float(E2, 53, 11)
    rule E1:Int		==	E2:Int		=>	E1						==Int		E2
    rule E1:Float	==	E2:Float	=>	E1						==Float		E2
    rule E1:Int		==	E2:Float	=>	Int2Float(E1, 53, 11)	==Float		E2
    rule E1:Float	==	E2:Int		=>	E1						==Float		Int2Float(E2, 53, 11)
    rule E1:Bool	==	E2:Bool		=>	E1						==Bool		E2
    rule E1:String	==	E2:String	=>	E1						==String	E2
    rule E1:Int		!=	E2:Int		=>	E1						=/=Int		E2
    rule E1:Float	!=	E2:Float	=>	E1						=/=Float	E2
    rule E1:Int		!=	E2:Float	=>	Int2Float(E1, 53, 11)	=/=Float	E2
    rule E1:Float	!=	E2:Int		=>	E1						=/=Float	Int2Float(E2, 53, 11)
    rule E1:Bool	!=	E2:Bool		=>	E1						=/=Bool		E2
    rule E1:String	!=	E2:String	=>	E1						=/=String	E2
    rule E1:Int		&	E2:Int		=>	E1						&Int		E2
    rule E1:Bool	&	E2:Bool		=>	E1						andBool		E2
    rule E1:Int		^	E2:Int		=>	E1						xorInt		E2
    rule E1:Bool	^	E2:Bool		=>	E1						xorBool		E2
    rule E1:Int		|	E2:Int		=>	E1						|Int		E2
    rule E1:Bool	|	E2:Bool		=>	E1						orBool		E2
endmodule