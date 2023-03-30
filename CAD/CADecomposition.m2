newPackage(
    "CADecomposition",
    Version => "0.1",
    Date => "29/03/2023",
    Headline => "Cylindrical Algebraic Decomposition",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    PackageExports => {"Elimination"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {"LazardProjection",
"FactorsInList",
"factors"}

-* Code section *-

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
    print("Unflattend list of factors:", L0);
    L1 := flatten(L0);
    L2 := L1/first//unique;
    L3 := select(L2, p -> #support p>0 )
    )
///


leadCoefficient(RingElement, RingElement) := (p, v) -> (
        d := degree(v,p);	
	contract(v^d,p)
	)
	    
LazardProjection = method()
LazardProjection(List, RingElement) := (L,v) -> (
        L0 := select(L, p -> not member(v,support(p)));
        print L0;
        L = select(L, p -> member(v,support(p)));
        print L;
        L1 := for p in L list leadCoefficient(p,v);		
        print L1;
	L2 := for p in L list discriminant(p,v);	
        print L2;
	L3 := for p in subsets(L,2) list resultant(p_0,p_1,v);			    
        print L3;
	FactorsInList(L0|L1|L2|L3)
	)

-* Documentation section *-
beginDocumentation()

doc ///
Key
  CADecomposition
Headline
  Cylindrical Algebraic Decomposition
Description
  Text
SeeAlso
///

 ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  SeeAlso
///

doc ///
  Key
    (LazardProjection, List, RingElement)
    LazardProjection
  Headline
    Computes the Lazard projection with respect to a variable.
  Usage
    LazardProjection(L,v)
  Inputs
    L:List
      of polynomials all in the same ring
    v:RingElement
      a variable in the ring
  Outputs
    :List
      list of projected polynomials not involving $v$
  Description
    Text
      Here we will say what the Lazard projection is
    Example
      R=QQ[x1,x2,x3]
      f0=x1*x2
      f1=x1^2*x2-x1*x3+x3^3
      f2=x2^2*x3+x3
      L={f0,f1,f2}
      L2 = LazardProjection(L,x1)
  SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  L2 = LazardProjection(L,x1)
  answer = {x3,x2,4*x2*x3-1,x2^2+1}
  assert(sort L2 === sort answer)
///

end--

-* Development section *-
restart
debug needsPackage "CADecomposition"
needsPackage "CADecomposition"
check "CADecomposition"

uninstallPackage "CADecomposition"
restart
installPackage "CADecomposition"
viewHelp "CADecomposition"
