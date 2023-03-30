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

export {"lazardProjection",
"factorsInList",
"factors",
"samplePoints",
"leadCoefficient",
"fullProjection",
"cell",
"evalPolyList"
}

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

-- finds the support of a list of Polynomials
support(List) := (L) -> (
    unique(flatten(L/support))
    )

///
	Factorising list of Polynomials into List of RingElements
	Input:
		L: List of polynomials,
	Output:
		List {g_1, \dots , g_m} of unrepeated factors of all polynomials in L
///
factorsInList = method()
factorsInList(List) := (L) -> (
    L0 := apply(L, p -> factors(p));
    -- print("Unflattend list of factors:", L0);
    L1 := flatten(L0);
    L2 := L1/first//unique;
    L3 := select(L2, p -> #support p>0 )
    )


-- Finds the lead coefficient of a ring element with respect to a variable
leadCoefficient(RingElement, RingElement) := (p, v) -> (
        d := degree(v,p);	
	contract(v^d,p)
	)

--    
lazardProjection = method()
lazardProjection(List, RingElement) := (L,v) -> (
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
	factorsInList(L0|L1|L2|L3)
	)

-- Creates a full Lazard projection
fullProjection = method()
fullProjection(List) := (L) -> (
    -- List is list of multivariate polynomials
    S = {L};
    while length(support(L)) > 1 do (
        L = lazardProjection(L, (support(L))_0);
        S = append(S,L);
        );
    S
    )

-- Given the list of lists of polynomials that the projection returns creates a CAD in a tree-like hash structure
-- starting from the point p given. i is the level and could be deduced from p but it is sent to ease understanding
cell = method()
cell(List, MutableHashTable, Number) := (S,p,i) -> (
    h = new MutableHashTable;
    -- HashTable is a point in i variables 
    -- List is a list of lists of polynomials, the first list of polys with i+1 variables
    L = evalPolyList(S_i, p); -- S is the list of lists of polynomials
    -- This function evaluates the point p into the polynomials of S_i
    v = support(L);
    samplePoints = RootIsolation(L);
    SNew = drop(S,1)
    for samplePoint in samplePoints (
        pNew = p
        pNew#v = samplePoint
        h#samplePoint = cell(S,pNew,i+1)
        )
    )

///
	Root Isolation for Several Polynomials:
	Input:
		L: List of polynomials,
		r: integer, rational or real number
///

samplePoints = method()
loadPackage "RealRoots";
for A in {ZZ,QQ,RR} do
samplePoints(List,A) := (L,r) -> (
    h=product L;
    -- print h;
    L  := realRootIsolation(h,r);
    print("root isolating intervals", L);
    L1:=for i from 1 to #L-1 list (L_(i-1)_1+L_i_0)/2;
    L2:=append(prepend(L_0_0,L1),L_(#L-1)_1)
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
    (lazardProjection, List, RingElement)
    lazardProjection
  Headline
    Computes the Lazard projection with respect to a variable.
  Usage
    lazardProjection(L,v)
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
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      L2 = lazardProjection(L,x1)
  SeeAlso
///

doc ///
  Key
    (factors, RingElement)
    factors
  Headline
    Returns a list of two element lists containing its factors and the exponents.
  Usage
    factors(p)
  Inputs
    p:polynomials in a ring
  Outputs
    :List
      list of lists its factors and its exponents
  Description
    Text
      This function breaks a RingElement into its factors
    Example
      R=QQ[x1,x2,x3]
      p=x1^3x2^3x3-4x1^2x2^3x3-x1^2x2^2x3^2+x1^2x2^2x3+4x1x2^3x3+4x1x2^2x3^2-4x1x2^2x3-4x2^2x3^2+4x2^2x3
      factors(p)
  SeeAlso
///

doc ///
  Key
    (factorsInList, List)
    factorsInList
  Headline
    Returns the factors that appear in a list of RingElements
  Usage
    factorsInList(L)
  Inputs
    L:List
        list of RingElements
  Outputs
    :List
      list of lists its factors and its exponents
  Description
    Text
      This function returns all the factors that appear in a list of RingElements without considering how many times they appear and ignoring the coefficients.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      factorsInList(L)
  SeeAlso
///

///
  Key
    (leadCoefficient, RingElement, RingElement)
    leadCoefficient
  Headline
    Finds the lead coefficient of a ring element with respect to a variable.
  Usage
    leadCoefficient(p,v)
  Inputs
    p:RingElement
    v:RingElement
      a variable in the ring
  Outputs
    :RingElement
  Description
    Text
      The leading coefficient of a RingElement with respect to a variable is returned.
    Example
      R=QQ[x1,x2,x3]
      p=x1^2*x2-x1*x3+x3^3
      lazardProjection(p,x1)
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
  L2 = lazardProjection(L,x1)
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
