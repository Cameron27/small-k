requires "../Core/additional-syntax.k"

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


    rule E1:MInt{64}    *	E2:MInt{64}	=>	E1									*MInt		E2
    rule E1:Float		*	E2:Float	=>	E1									*Float		E2
    rule E1:MInt{64}	*	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	*Float		E2
    rule E1:Float		*	E2:MInt{64}	=>	E1									*Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	/	E2:MInt{64}	=>	E1									/sMInt		E2
        requires E2 =/=MInt 0p64
    rule E1:Float		/	E2:Float	=>	E1									/Float		E2
        requires E2 =/=Float 0d
    rule E1:MInt{64}	/	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	/Float		E2
        requires E2 =/=Float 0d
    rule E1:Float		/	E2:MInt{64}	=>	E1									/Float		Int2Float(MInt2Signed(E2), 53, 11)
        requires E2 =/=MInt 0p64
    rule E1:MInt{64}	%	E2:MInt{64}	=>	E1									%sMInt		E2
        requires E2 =/=MInt 0p64
    rule E1:MInt{64}    +	E2:MInt{64}	=>	E1									+MInt		E2
    rule E1:Float		+	E2:Float	=>	E1									+Float		E2
    rule E1:MInt{64}	+	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	+Float		E2
    rule E1:Float		+	E2:MInt{64}	=>	E1									+Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:String		+	E2:String	=>	E1									+String		E2
    rule E1:MInt{64}	-	E2:MInt{64}	=>	E1									-MInt		E2
    rule E1:Float		-	E2:Float	=>	E1									-Float		E2
    rule E1:MInt{64}	-	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	-Float		E2
    rule E1:Float		-	E2:MInt{64}	=>	E1									-Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	<	E2:MInt{64}	=>	E1									<sMInt		E2
    rule E1:Float		<	E2:Float	=>	E1									<Float		E2
    rule E1:MInt{64}	<	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	<Float		E2
    rule E1:Float		<	E2:MInt{64}	=>	E1									<Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	<=	E2:MInt{64}	=>	E1									<=sMInt		E2
    rule E1:Float		<=	E2:Float	=>	E1									<=Float		E2
    rule E1:MInt{64}	<=	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	<=Float		E2
    rule E1:Float		<=	E2:MInt{64}	=>	E1									<=Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	>	E2:MInt{64}	=>	E1									>sMInt		E2
    rule E1:Float		>	E2:Float	=>	E1									>Float		E2
    rule E1:MInt{64}	>	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	>Float		E2
    rule E1:Float		>	E2:MInt{64}	=>	E1									>Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	>=	E2:MInt{64}	=>	E1									>=sMInt		E2
    rule E1:Float		>=	E2:Float	=>	E1									>=Float		E2
    rule E1:MInt{64}	>=	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	>=Float		E2
    rule E1:Float		>=	E2:MInt{64}	=>	E1									>=Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:MInt{64}	==	E2:MInt{64}	=>	E1									==MInt		E2
    rule E1:Float		==	E2:Float	=>	E1									==Float		E2
    rule E1:MInt{64}	==	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	==Float		E2
    rule E1:Float		==	E2:MInt{64}	=>	E1									==Float		Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:Bool		==	E2:Bool		=>	E1									==Bool		E2
    rule E1:String		==	E2:String	=>	E1									==String	E2
    rule E1:MInt{64}	!=	E2:MInt{64}	=>	E1									=/=MInt		E2
    rule E1:Float		!=	E2:Float	=>	E1									=/=Float	E2
    rule E1:MInt{64}	!=	E2:Float	=>	Int2Float(MInt2Signed(E1), 53, 11)	=/=Float	E2
    rule E1:Float		!=	E2:MInt{64}	=>	E1									=/=Float	Int2Float(MInt2Signed(E2), 53, 11)
    rule E1:Bool		!=	E2:Bool		=>	E1									=/=Bool		E2
    rule E1:String		!=	E2:String	=>	E1									=/=String	E2
    rule E1:MInt{64}	&	E2:MInt{64}	=>	E1									&MInt		E2
    rule E1:Bool		&	E2:Bool		=>	E1									andBool		E2
    rule E1:MInt{64}	^	E2:MInt{64}	=>	E1									xorMInt		E2
    rule E1:Bool		^	E2:Bool		=>	E1									xorBool		E2
    rule E1:MInt{64}	|	E2:MInt{64}	=>	E1									|MInt		E2
    rule E1:Bool		|	E2:Bool		=>	E1									orBool		E2
endmodule