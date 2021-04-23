requires "additional-syntax.k"

module OPERATIONS
    imports ADDITIONAL-SYNTAX
    imports FLOAT

    context (HOLE => reval(HOLE)) * _
    context _ * (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) / _
    context _ / (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) % _
    context _ % (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) + _
    context _ + (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) - _
    context _ - (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) < _
    context _ < (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) <= _
    context _ <= (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) > _
    context _ > (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) >= _
    context _ >= (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) == _
    context _ == (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) != _
    context _ != (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) & _
    context _ & (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) ^ _
    context _ ^ (HOLE => reval(HOLE))
    context (HOLE => reval(HOLE)) | _
    context _ | (HOLE => reval(HOLE))

    rule TInt		*	TInt		=> TInt
    rule TDouble	*	TDouble	    => TDouble
    rule TInt		*	TDouble	    => TDouble
    rule TDouble	*	TInt		=> TDouble
    rule TInt		/	TInt		=> TInt
    rule TDouble	/	TDouble	    => TDouble
    rule TInt		/	TDouble	    => TDouble
    rule TDouble	/	TInt		=> TDouble
    rule TInt		%	TInt		=> TInt
    rule TInt		+	TInt		=> TInt
    rule TDouble	+	TDouble	    => TDouble
    rule TInt		+	TDouble	    => TDouble
    rule TDouble	+	TInt		=> TDouble
    rule TString	+	TString	    => TString
    rule TInt		-	TInt		=> TInt
    rule TDouble	-	TDouble	    => TDouble
    rule TInt		-	TDouble	    => TDouble
    rule TDouble	-	TInt		=> TDouble
    rule TInt		<	TInt		=> TBool
    rule TDouble	<	TDouble	    => TBool
    rule TInt		<	TDouble	    => TBool
    rule TDouble	<	TInt		=> TBool
    rule TInt		<=	TInt		=> TBool
    rule TDouble	<=	TDouble	    => TBool
    rule TInt		<=	TDouble	    => TBool
    rule TDouble	<=	TInt		=> TBool
    rule TInt		>	TInt		=> TBool
    rule TDouble	>	TDouble	    => TBool
    rule TInt		>	TDouble	    => TBool
    rule TDouble    >	TInt		=> TBool
    rule TInt       >=	TInt		=> TBool
    rule TDouble	>=	TDouble	    => TBool
    rule TInt		>=	TDouble	    => TBool
    rule TDouble	>=	TInt		=> TBool
    rule TInt		==	TInt		=> TBool
    rule TDouble	==	TDouble	    => TBool
    rule TInt		==	TDouble	    => TBool
    rule TDouble	==	TInt		=> TBool
    rule TBool	    ==	TBool		=> TBool
    rule TString	==	TString	    => TBool
    rule TInt		!=	TInt		=> TBool
    rule TDouble	!=	TDouble	    => TBool
    rule TInt		!=	TDouble	    => TBool
    rule TDouble	!=	TInt		=> TBool
    rule TBool	    !=	TBool		=> TBool
    rule TString	!=	TString	    => TBool
    rule TInt		&	TInt		=> TInt
    rule TBool	    &	TBool		=> TBool
    rule TInt		^	TInt		=> TInt
    rule TBool	    ^	TBool		=> TBool
    rule TInt		|	TInt		=> TInt
    rule TBool	    |	TBool		=> TBool
endmodule