///
	Factorising (list of) Polynomials into (List of) RingElements
	Input:
		p: polynomial
	Output:
		{ {g_1,e_1}, \dots,{g_m,e_m},{coeff,1}}, g_i: facotrs, e_i: exponents, last e,ement is the coeff w exponent 1
///
factors = method()
factors(RingElement) := (p) -> (
  L := p//factor//toList/toList;
  print L
  )

///
	Factorising list of Polynomials into List of RingElements
	Input:
		L: List of polynomials,
	Output:
		List {g_1, \dots , g_m} of unrepeated factors of all polynomials in L
///
FactorsInList = method()
FactorsInList(List) := (L) -> (
    L0 := apply(L, p -> factors(p));
    -- print("Unflattend list of factors:", L0);
    L1 := flatten(L0);
    L2 := L1/first//unique;
    L3 := select(L2, p -> #support p>0 )
    )

/// Test
    R=QQ[x1,x2,x3]
    f0=x1*x2
    f1=x1^2*x2-x1*x3+x3^3
    f2=x2^2*x3+x3
    f3=5*x1
    L={f0,f1,f2,f3}
   FactorsInList(L)
///
