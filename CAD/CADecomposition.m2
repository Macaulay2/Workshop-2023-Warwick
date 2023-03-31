newPackage(
    "CADecomposition",
    Version => "0.1",
    Date => "29/03/2023",
    Headline => "Cylindrical Algebraic Decomposition",
    Authors => {{ Name => "del Rio, T.", Email => "delriot@coventry.ac.uk", HomePage => "https://pureportal.coventry.ac.uk/en/persons/tereso-del-r%C3%ADo-almajano"},	{ Name => "Rahkooy, H.", Email => "rahkooy@maths.ox.ac.uk", HomePage => "https://people.maths.ox.ac.uk/rahkooy/"},	{ Name => "Lee, C.", Email => "cel34@bath.ac.uk", HomePage => "https://people.bath.ac.uk/cel34/"}},
    PackageExports => {"Elimination", "RealRoots"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {"factors",
"factorsInList",
"evalPoly",
"evalPolyList",
"leadCoefficientt",
"lazardProjection",
"projectionPhase",
"liftingPoint",
"samplePoints",
"openCAD",
"gmodsHeuristic"
}

-* Code section *-

-- factors a given polynomial
factors = method()
factors(RingElement) := (p) -> (
  L := p//factor//toList/toList
  -- print L
  )

-- finds the support of a list of Polynomials
support(List) := (L) -> (
    unique(flatten(L/support))
    )

-- find factors of all polynomials in a list, removing repetition
factorsInList = method()
factorsInList(List) := (L) -> (
    L0 := apply(L, p -> factors(p));
    -- print("Unflattend list of factors:", L0);
    L1 := flatten(L0);
    L2 := L1/first//unique;
    L3 := select(L2, p -> #support p>0 )
)

-- Evaluates the given RingElement in a point given by a MutableHashTable.
evalPoly = method()
evalPoly(RingElement,MutableHashTable) := (p, alpha) -> (
        for k in keys(alpha) do(
          -- print("variable", k);
          p=sub(p, {k => alpha#k});
        );
	p
      )

-- Evaluates a List of RingElement in a point given by a MutableHashTable
evalPolyList = method()
evalPolyList(List,MutableHashTable) := (S, alpha) -> (
  S1 := for p in S list
    evalPoly(p,alpha);
  S1
)

-- Finds the lead coefficient of a ring element with respect to a variable
leadCoefficientt = method()
leadCoefficientt(RingElement, RingElement) := (p, v) -> (
  d := degree(v,p);	
  contract(v^d,p)
)

-- Choose the next variable to project according to the heuristic gmods
gmodsHeuristic = method()
gmodsHeuristic(List) := (L) -> (
  vars := support(L);
  -- print vars;
  gmodsVar := vars_0;
  minGmods := sum(for p in L list degree(vars_0, p));
  for var in vars do (
    -- print var;
    newGmods := sum(for p in L list degree(var, p));
    if newGmods < minGmods then (
      gmodsVar = var;
      minGmods = newGmods;
      );
    );
  gmodsVar
  )

-- Does one step of the projection phase
lazardProjection = method()
lazardProjection(List, RingElement) := (L,v) -> (
  L0 := select(L, p -> not member(v,support(p)));
  L = select(L, p -> member(v,support(p)));
  L1 := for p in L list leadCoefficientt(p,v);
	L2 := for p in L list discriminant(p,v);
	L3 := for p in subsets(L,2) list resultant(p_0,p_1,v);
	factorsInList(L0|L1|L2|L3)
	)

-------
-- Creating optional argument, add later
-------

-- -- Does one step of the projection phase
-- lazardProjection = method(Options => {Trailing => false})
-- lazardProjection(List, RingElement) := opts -> (L,v) -> (
--     usetrailing := opts.Trailing;
--     L0 := select(L, p -> not member(v,support(p)));
--     L = select(L, p -> member(v,support(p)));
--     L1 := for p in L list leadCoefficientt(p,v);
-- 	L2 := for p in L list discriminant(p,v);
-- 	L3 := for p in subsets(L,2) list resultant(p_0,p_1,v);
--     if usetrailing do (
--         -- compute trailing coefficient
--         L4 := for p in L list contract(v^0,p);
--         allProj := L0|L1|L2|L3|L4;
--     )
--     else do (
--         allProj := L0|L1|L2|L3;
--     )
-- 	allProj
-- )

-- Creates a full Lazard projection
projectionPhase = method()
projectionPhase(List) := (L) -> (
    -- List is list of multivariate polynomials
    S := {L};
    while length(support(L)) > 1 do (
      -- print(L);
      var := gmodsHeuristic(support(L))
      L = lazardProjection(L, var); -- ideally doing gmods here
      S = prepend(L,S);
      );
    S
    )

-- Given the list of lists of polynomials that the projection returns creates a CAD in a tree-like hash structure
-- starting from the point p given. i is the level and could be deduced from p but it is sent to ease understanding
liftingPoint = method()
liftingPoint(List, MutableHashTable) := (S,p) -> (
    -- HashTable is a point in i variables 
    -- List is a list of lists of polynomials, the first list of polys with i+1 variables
    cell := new MutableHashTable;
    cell#"point" = p;
    i := #keys(p);
    -- we check if all the variables have been given a value already
    if i >= length(S) then return cell; -- if so just return an empty MutableHashTable
    L := evalPolyList(S_i, p); -- S is the list of lists of polynomials
    cell#"polynomials"=L;
    -- This function evaluates the point p into the polynomials of S_i
    if #support(L)!=1 then error "Expected list of polynomials to have a single variable as support";
    v := (support(L))_0;
    -- print(L);
    newSamplePoints := samplePoints(L);
    SNew := drop(S,1);
    for samplePoint in newSamplePoints do (
        pNew := p;
        pNew#v = samplePoint;
        cell#samplePoint = liftingPoint(S,pNew);
        );
    cell
    )

-- Given a list of univariate polynomials, samplePoints prduces sample points for the cells (seperating the roots)
samplePoints = method()
-- for A in {ZZ,QQ,RR} do
-- samplePoints(List,A) := (L,r) -> (
   -- We consider r=1 for the size of the interval
samplePoints(List) := (L) -> (
    A := QQ(monoid[support(L)]);
    h:=sub(product L, A);
    -- print("L"); print L;
    -- print h;
    ourRoots := realRootIsolation(h,1); -- when RealRoots is evaluating h they get an element of R, not a number
    -- print("root isolating intervals", ourRoots);
    L1:=for i from 1 to #ourRoots-1 list (ourRoots_(i-1)_1+ourRoots_i_0)/2;
    if #ourRoots>=1 then (
      L2:=append(prepend(ourRoots_0_0,L1),ourRoots_(#ourRoots-1)_1);
      return L2 );
    return L1
    )


-- Does the open CAD
openCAD = method()
openCAD(List) := (L) -> (
  S := projectionPhase(L);
  p := new MutableHashTable;
  liftingPoint(S,p)
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

doc ///
  Key
    (evalPoly, RingElement, MutableHashTable)
    evalPoly
  Headline
    Evaluates the given polynomial with respect to the given sample point.
  Usage
    evalPoly(p,alpha)
  Inputs
    p:RingElement
      polynomial as a RingElement
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :RingElement
      RingElement describing the polynomial evaluated at the sample point.
  Description
    Text
      Given the polynomial (p) and sample point (alpha) it evaluates the polynomial at the sample point and returns that polynomial. This is used in the lifting phase of the CAD, where a polynomial in $k$ variables is evaluated at a point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return a univariate polynomial in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  p=x1^2*x0-2*x3*x2
	  evalPoly(p,alpha)
  SeeAlso
///

doc ///
  Key
    (evalPolyList, List, MutableHashTable)
    evalPolyList
  Headline
    Given a list of polynomials (S) and a sample point (alpha), returns the polynomials of S evaluated at alpha.
  Usage
    evalPolyList(S,alpha)
  Inputs
    S:List
      list of polynomials as RingElements
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :List
      List of RingElements describing the polynomials in S evaluated at the sample point.
  Description
    Text
      Given the list of polynomial (S) and sample point (alpha) it evaluates the list polynomial at the sample point and returns that polynomial, by calling evalPoly on each polynomial in S. 	  This is used in the lifting phase of the CAD, where the polynomials in set of polynomials in $k$ variables are evaluated at a point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return univariate polynomials in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  S = {x1^2*x0-2*x3*x2,x1^3*x0*x2+x3}
	  evalPolyList(S,alpha)
  SeeAlso
///


doc ///
  Key
    (samplePoints, List)
    samplePoints
  Headline
    Computes a list of sample points in each cell that isolate the roots
  Usage
    samplePoints(L)
  Inputs
    L:List
      of polynomials in one variable
  Outputs
    :List
      list of points in ZZ/QQ/RR, depending on the defining coefficient field
  Description
    Text
      Sample points are the points in each cell of the CAD. Such points are computed via isolating real roots of univariate polynomials obtained after projecting wrt all variables.
    Example
      R=QQ[x]
      f=x^2-1
      g=x^3-1
      L1={f,g}
      samplePoints(L1)

      f1=5*x^3+1
      g1=x^2-1
      h1=1/2*x^5+3*x-1
      L2={f1,g1,h1}
      S:=samplePoints(L2)
   
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
      Lazard projection is an operation that takes a variable $v$ set of polynomials in n variables and returns a set of polynomials without that variable. It is used in the projection phase of Cylindrical Algebraic Decomposition and it consists of the leading and trailing coefficients of the given polynomials with respect to (w.r.t) $v$, the discriminant of the given polynomials w.r.t $v$ and the resultant between any pair of given polynomials w.r.t $v$. For openCAD, the trailing coefficients are not needed.
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
    p:RingElement
      polynomial in a ring
  Outputs
    :List
      list of lists of the factors and their exponents, last element is the constant with exponent 1
  Description
    Text
      This function breaks a RingElement into its factors
    Example
      R=QQ[x1,x2,x3]
      p=x1^3*x2^3*x3-4*x1^2*x2^3*x3-x1^2*x2^2*x3^2+x1^2*x2^2*x3+4*x1*x2^3*x3+4*x1*x2^2*x3^2-4*x1*x2^2*x3-4*x2^2*x3^2+4*x2^2*x3
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

doc ///
  Key
    (leadCoefficientt, RingElement, RingElement)
    leadCoefficientt
  Headline
    Finds the lead coefficient of a ring element with respect to a variable.
  Usage
    leadCoefficientt(p,v)
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
      leadCoefficientt(p,x1)
  SeeAlso
///

doc ///
  Key
    (liftingPoint, List, MutableHashTable)
    liftingPoint
  Headline
    Given the projection phase of a CAD (S) it returns an OpenCAD above the point given.
  Usage
    liftingPoint(S,p)
  Inputs
    S:List
      list of lists of RingElements
    p:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :MutableHashTable
      MutableHashTable describing an OpenCAD
  Description
    Text
      Given the projection phase of a CAD (S) it creates an Open Cylindrical Algebraic Decomposition. It basically breaks the space into cells where the sign of the RingElements in S_(-1) are constant.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      pts = new MutableHashTable
      pts#x1 = 1
      pts#x2 = 3
      liftingPoint(L,pts)
  SeeAlso
///

doc ///
  Key
    (openCAD, List)
    openCAD
  Headline
    Given a list of polynomials, an open CAD of those polynomials is returned. (main algorithm)
  Usage
    openCAD(L)
  Inputs
    L:List
      of polynomials all in the same ring
  Outputs
    :MutableHashTable
      describing an open CAD of the given list of polynomials
  Description
    Text
      An open CAD is a mathematical object that decomposes the space into cells in which the given polynomials are sign invariant.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      openCAD(L)
  SeeAlso
///

-* Test section *-
TEST /// -* factors test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  p=x1^3*x2^3*x3-4*x1^2*x2^3*x3-x1^2*x2^2*x3^2+x1^2*x2^2*x3+4*x1*x2^3*x3+4*x1*x2^2*x3^2-4*x1*x2^2*x3-4*x2^2*x3^2+4*x2^2*x3
  F = factors(p)
  answer = {{x3, 1}, {x2, 2}, {x1 - 2, 2}, {x1*x2 - x3 + 1, 1}}
  assert(sort F === sort answer)
///

TEST /// -* factorsInList test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,p2}
  F = factorsInList(L) 
  answer = {x2,x1,x1^2*x2+x3^3-x1*x3,x3,x2^2+1}
  assert(sort F === sort answer)
///

TEST /// -* evalPoly test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  p = new MutableHashTable
  p#x1 = 1
  p#x2 = 3
  E = evalPoly(f1,p)
  answer = 3-x3+x3^3
  assert(E == answer)
///

TEST /// -* evalPolyList test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  p = new MutableHashTable
  p#x1 = 1
  p#x2 = 3
  E = evalPolyList(L,p)
  answer = {3, 3-x3+x3^3, 9*x3+x3}
  assert(E == answer)
///

TEST /// -* leadCoefficientt test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  p=x1^2*x2-x1*x3+x3^3
  L = leadCoefficientt(p,x1)
  answer = x2
  assert(L == answer)
///

TEST /// -* lazardProjection test *-
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

TEST /// -* projectionPhase test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  P = projectionPhase(L)
  answer = {{x2^2+1,x2}, {x3,x2^2+1,x2,4*x2*x3-1}, {x1*x2,x1^2*x2+x3^3-x1*x3,x2^2*x3+x3}}
  assert(sort P === sort answer)
///

TEST /// -* liftingPoint test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1*x2+x3^2
  L={p0,p1}
  P = projectionPhase(L)
  pts = new MutableHashTable
  pts#x1 = 1
  pts#x2 = 3
  LP = liftingPoint(P,pts)
  peek LP
  
  
  H = new MutableHashTable
  H2 = new MutableHashTable
  H2#x3 = 0
  H2#x2 = 3
  H2#x1 = 1  
  H#point = H2  
  
  
  answer = H
  assert(LP == answer)
///

TEST /// -* samplePoints test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x]
  f=x^2-1
  g=x^3-1
  L1={f,g}
  S = samplePoints(L1)
  answer = {-2, -1/2, 1}
  assert(S == answer)
///

TEST /// -* openCAD test *-
-- test code and assertions here
-- may have as many TEST sections as needed
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,p2}
  openCAD(L)
  answer = {}
  assert(S == answer)
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
