newPackage(
    "CADecomposition",
    Version => "1.0.1",
    Date => "11/04/2024",
    Headline => "A package for performing (open) Cylindrical Algebraic Decompositions.",
    Authors => {
	{ Name => "del Rio, T.", 
	  Email => "delriot@coventry.ac.uk", 
	  HomePage => "https://pureportal.coventry.ac.uk/en/persons/tereso-del-r%C3%ADo-almajano"},	
        { Name => "Rahkooy, H.", 
	  Email => "rahkooy@maths.ox.ac.uk", 
	  HomePage => "https://people.maths.ox.ac.uk/rahkooy/"},	
        { Name => "Lee, C.", 
	  Email => "cel34@bath.ac.uk", 
	  HomePage => "https://people.bath.ac.uk/cel34/"}
        },

    Keywords => {"Real Algebraic Geometry"},
    PackageExports => {"Elimination", "RealRootsNew"}, --when RealRoots is updated, rename "RealRootsNew" to "RealRoots".
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

--"A package can contain the code for many functions, only some of which should be made visibxle to the user.
--The function export allows one to specify which symbols are to be made visible."
--At the end, trim this down to only the ones useful for people using the package.
export {
    "factors",
    "factorsInList",
    "evalPolys",
    "leadCoeff",
    "gmodsHeuristic",
    "lazardProjection",
    "projectionPhase",
    "samplePoints",
    "liftingPoint",
    "openCAD",
    "positivePoint",
    "findPositiveSolution",
"hashify"
}

-* Code section *-

-- factors a given polynomial
factors = method()
factors(RingElement) := (p) -> (
    p//factor//toList/toList
  )

-- finds the support of a list of Polynomials
-- overloads original command to return the combined support of a list of polynomials.
support(List) := (L) -> (
    for p in L do
      if liftable(p,QQ) then L = delete(p,L); --added to catch new output from evalPolys
    unique(flatten(L/support))
    )

-- find factors of all polynomials in a list, removing repetition
factorsInList = method()
factorsInList(List) := (L) -> (
    FL := flatten(apply(L, p -> factors(p))); --calls 'factors' on each element of L and combines these into a single list of pairs.
    FL = FL/first//unique; --Reduces list to only the unique factors, removing multiplicity.
    FL = select(FL, p -> #support p>0 ) --removes any constants.
)

-- Evaluates the given RingElement or List of RingElements at a point given by a MutableHashTable.
evalPolys = method()
evalPolys(RingElement,MutableHashTable) := (p, alpha) -> (
    for k in keys(alpha) do(
      p=sub(p, {k => alpha#k}); --substitute in all of the values for the variables specified in alpha.
    );
    if liftable(p,QQ) then p = lift(p,QQ); --if the output is a constant, lift it.
      p
    )
evalPolys(List,MutableHashTable) := (L, alpha) -> (
    E := for p in L list
      evalPolys(p,alpha); --for a list of polynomials, call evalPolys on each polynomial in the list and return the evaluated list.
    E
    )

-- Finds the lead coefficient of a ring element with respect to a variable
leadCoeff = method()
leadCoeff(RingElement, RingElement) := (p, v) -> (
  d := degree(v,p); --obtain the highest degree of the specified variable
  contract(v^d,p) --return the coefficient of the leading term.
)

-- Choose the next variable to project according to the heuristic gmods
gmodsHeuristic = method()
gmodsHeuristic(List, List) := (L, variables) -> (
  gmodsVar := variables_0; --start with the first variable in the list.
  minGmods := sum(for p in L list degree(gmodsVar, p)); --sum of variable degree in each polynomial.
  for var in variables do (
    newGmods := sum(for p in L list degree(var, p)); --for each other variable, do the same
    if newGmods < minGmods then ( --if this variable has a smaller degree sum, set it as the new variable, and update minGmods.
      gmodsVar = var; 
      minGmods = newGmods;
      );
    );
  gmodsVar
  )

-- Does one step of the projection phase
lazardProjection = method()
lazardProjection(List, RingElement) := (L,v) -> (
  L = factorsInList(L); --ensure input polynomials are irreducible and pairwise relatively prime.
  L0 := select(L, p -> not member(v,support(p))); --polynomials not relying on v
  L = select(L, p -> member(v,support(p))); --remove polynomials p not relying on v 
  -- these would create redundant calculations (resultants would be a power of p,
  -- discriminants and leading coefficient would be 0 and trailing coefficient would be p
  -- so we will just slot these back in later)
  -- "return the parts of each poly p in L that rely on v"
        L1 := for p in L list leadCoeff(p,v); --leading coefficients
        L2 := for p in L list p-v*contract(v,p); --trailing coefficients
	L3 := for p in L list discriminant(p,v); --discriminants
	L4 := for p in subsets(L,2) list resultant(p_0,p_1,v); --resultants
	factorsInList(L0|L1|L2|L3|L4) -- combine these into one list, as squarefree factors.
	)

-- Creates a full Lazard projection
projectionPhase = method()
projectionPhase(List) := (L) -> (
    L = factorsInList(L);
    S := {L};
    variables := support(L); --initial variables, the ones chosen already will be dropped
    ordering := {}; -- this will contain the variable ordering chosen
    while length(variables) > 1 do ( --project recursively until you are left with univariate polynomials
      v := gmodsHeuristic(L, variables); --identify variable to project away.
      L = lazardProjection(L, v); --get projection in v
      variables = select(variables,n -> n != v); -- variable chosen is dropped
      S = prepend(L, S); --projection polynomials are added to S.
      ordering = prepend(v, ordering); --variable projected is added to ordering.
    );
    ordering = prepend(variables_0, ordering); -- the remaining variable is added to ordering.
    (S, ordering)
    )

-- Given a nonempty list of univariate polynomials, samplePoints prduces sample points for the cells (seperating the roots)
samplePoints = method()
samplePoints(List) := (L) -> (
    if L=={} then error "Error: Expected non-empty list";
    A := QQ(monoid[support(L)]);
    h:=sub(product L, A);
    intervalSize := 1; 
    ourRoots := realRootIsolation(h,intervalSize); --call RealRoots:-realRootIsolation (isolates real solutions of h in intervals of width at most 1)
    if length(ourRoots)==0 then (
        SP := {}; -- if the polynomials have no roots, set SP to empty list.
      )
      else (
    -- if two consecutive intervals have a shared start/end point that is a root then refine intervals:
      for i from 0 to #ourRoots-2 do (
        while (ourRoots_i_1)==(ourRoots_(i+1)_0) and sub(h,{(support h)#0=>ourRoots_i_1})==0 do (
          intervalSize = intervalSize/2;
          ourRoots = realRootIsolation(h,intervalSize);
        );
      );
      SP = for i from 0 to #ourRoots-2 list (ourRoots_i_1+ourRoots_(i+1)_0)/2; --if there is only one root, this correctly returns an empty list.
      -- Add the beginning of the first interval and the end of the last interval to the list, but each of which -+1 in order to avoid them being a root:
      -- (putting all roots into QQ - get +-1 in ZZ if one root
      SP = {((min (flatten ourRoots))-1)_QQ}|SP|{((max (flatten ourRoots))+1)_QQ};
    );
    SP
  )

-- Given the list of lists of polynomials that the projection returns creates a CAD in a tree-like hash structure
-- starting from the point p given. i is the level and could be deduced from p but it is sent to ease understanding
liftingPoint = method()
liftingPoint(List, MutableHashTable, List) := (S, alpha, ordering) -> (
    -- List (S) is a list of lists of polynomials, representing the projection polynomials at each level, starting in one variable, up to
    -- the initial list of polynomials in n variables.
    -- HashTable (alpha) is a point in i variables
    -- List (ordering) is the variable ordering followed in the projection (the first i variables are the variables at level i)
    cell := new MutableHashTable;
    cell#"point" = alpha;
    i := #keys(alpha); --number of variables that have been assigned
    -- we check if all the variables have been given a value already
    if i >= length(S) then return cell; -- if so just return an empty MutableHashTable
    U := evalPolys(S_i, alpha); -- evaluating the polys in i+1 vars at point p (so U should be a set of univariate polynomials)
    cell#"polynomials"=U;
    --Check in case U is not univariate.
    if #support(U) > 1 then error ("Expected list of polynomials to have a single variable as support. The value of U is " | toString(U));
    v := ordering_i;
    newSamplePoints := samplePoints(U);
    for samplePoint in newSamplePoints do (
        alphaNew := copy alpha;
        alphaNew#v = samplePoint;
        cell#samplePoint = liftingPoint(S, alphaNew, ordering);
    );
    cell
    )

--project and lift the initial polynomials, performing a full open CAD.
openCAD = method()
openCAD(List) := (L) -> (
  (S, ordering) := projectionPhase(L);
  alpha := new MutableHashTable;
  liftingPoint(S, alpha, ordering)
)

-- Checks if there is a point in or above the given cell in which all the polynomials given in the list are strictly positive
positivePoint = method()
positivePoint(List, MutableHashTable) := (L, cell) -> (
    -- move down to bottom level, where all variables are evaluated.
    if length(keys(cell#"point"))<length(support(L)) then (
        for key in keys(cell) do(
            -- if the key is not "points" or "polynomials", call again 
            if not instance(key,String) then(
                result := positivePoint(L, cell#key);
                -- if the answer is a point (something different from null)
                if instance(result, HashTable) then(
                    return result
                );
            );
        )
    ) else (
        evaluations := evalPolys(L,cell#"point");
	evaluations = for e in evaluations list lift(e,QQ); --elements in list were in R and not treated as numbers, this fixes that.
        for e in evaluations list e>0; --see if positive or not
        if all(evaluations, elem->(elem>0)) then (
          return cell#"point"
        )
    );
    return "no point exists"
)

-- Checks if there is a point in which all the polynomials given in the list are strictly positive, and return it
findPositiveSolution = method()
findPositiveSolution(List) := (L) -> (
    result := positivePoint(L, openCAD(L));
    if instance(result, HashTable)
    then (true, hashify result)
    else (false, result)
)

-- Turns MutableHashTables into HashTables
hashify = method()
hashify(MutableHashTable) := (H) -> (
   hashTable for KV in pairs H list KV#0 => hashify(KV#1)
    )
hashify(HashTable) := (H) -> (
   hashTable for KV in pairs H list KV#0 => hashify(KV#1)
    )
hashify(List) := (H) -> (
    for x in H list hashify x
    )
hashify(MutableList) := (H) -> (
    for x in H list hashify x
    )
hashify(Thing) := (H) -> (H)

    
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
    (factors, RingElement)
    factors
  Headline
    Returns a list of pairs containing the polynomial's factors and exponents.
  Usage
    factors(p)
  Inputs
    p:RingElement
      polynomial in a ring.
  Outputs
    :List
      of list pairs containing the polynomial's factors and their exponents.
  Description
    Text
      This function breaks a RingElement into its factors, returning this as a list of pairs (factor and exponent).
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
     of polynomials in a ring.
  Outputs
    :List
      containing the factors of each polynomial, without multiplicity.
  Description
    Text
      This function returns all of the factors that appear in a list of RingElements, ignoring constants and multiplicity.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
      L={p0,p1,p2}
      factorsInList(L)
  SeeAlso
    factors
///

doc ///
  Key
    evalPolys
    (evalPolys, RingElement, MutableHashTable)
    (evalPolys, List, MutableHashTable)
  Headline
    Evaluates the given polynomial or list of polynomials with respect to the given sample point.
  Usage
    evalPolys(p,alpha)
    evalPolys(L,alpha)
  Inputs
    p:RingElement
      polynomial in a ring.
    L:List
      of polynomials in a ring.
    alpha:MutableHashTable
      point described using a mutable hash table where the keys are RingElements (variables in the ring) and the values are the associated sample point.
  Outputs
    :RingElement
      describing the polynomial evaluated at the sample point.
    :List
      of polynomials evaluated at the sample point.
  Description
    Text
      Given the polynomial (p) or list of polynomials (L) and sample point (alpha), evalPolys evaluates the 
      polynomial(s) at the sample point and returns the evaluated polynomial(s). 
      This is used in the lifting phase of the CAD, where a polynomial in k variables is evaluated at a 
      point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}]$ to return a univariate polynomial in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable;
	  alpha#x0 = 3, alpha#x1 = 4, alpha#x2 = 1;
	  p0=x1^2*x0-2*x3*x2
	  evalPolys(p0,alpha)
	  alpha1 := copy alpha;
	  alpha1#x3 = -2;
	  evalPolys(p0,alpha1)
	  
          p1=x0*(x1-1)*(x2-2)*(x3-3);
    	  L = {p0,p1}
	  evalPolys(L,alpha)
	  evalPolys(L,alpha1)
  SeeAlso
///

doc ///
  Key
    (leadCoeff, RingElement, RingElement)
    leadCoeff
  Headline
    Finds the lead coefficient of a ring element with respect to a variable.
  Usage
    leadCoeff(p,v)
  Inputs
    p:RingElement
      a polynomial in the ring.
    v:RingElement
      a variable in the ring.
  Outputs
    :RingElement
      the leading coefficient of p with respect to the variable v.
  Description
    Text
      The leading coefficient of a RingElement with respect to a variable is returned.
    Example
      R=QQ[x1,x2,x3]
      p=x1^2*x2-x1*x3+x3^3
      leadCoeff(p,x1)
  SeeAlso
///

doc ///
  Key
    (gmodsHeuristic, List, List)
    gmodsHeuristic
  Headline
    Uses the gmods heuristic to determine the next variable to project.
  Usage
    gmodsHeuristic(L,variables)
  Inputs
    L:List
      of polynomials in several variables.
    variables:List
      of variables in the polynomials provided.
  Outputs
    :RingElement
      the chosen variable to project.
  Description
    Text
      Given a list $L$ of polynomials in one or more variables, returns the variable with the lowest sum of degrees of the given polynomials. In case of tie, the 
      variable that appears earlier in support(L) is returned. This heuristic is motivated by the complexity analysis of CAD. Further information regarding this 
      heuristic can be found in "https://doi.org/10.1007/978-3-031-14788-3_17".
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3, p3=-x1*x2;
      L={p0,p1,p2,p3}
      gmodsHeuristic(L,support(L))
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
      of polynomials all in the same ring.
    v:RingElement
      a variable in the ring.
  Outputs
    :List
      of projected polynomials not involving v.
  Description
    Text
      Lazard projection is an operation that takes a variable v and a set L of polynomials in $n$ variables, and returns a set of polynomials 
      in the remaining $n-1$ variables, representing the significant points of the polynomials.
      This is used in the projection phase of Cylindrical Algebraic Decomposition, and consists of the leading and trailing coefficients of the given 
      polynomials w.r.t v, the discriminants of the polynomials w.r.t v and the resultants between each pair of polynomials 
      w.r.t v. For openCAD, the trailing coefficients are not needed.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
      L={p0,p1,p2}
      L2 = lazardProjection(L,x1)
  SeeAlso
    leadCoeff
    factorsInList
///

doc ///
  Key
    (projectionPhase, List)
    projectionPhase
  Headline
    Creates a full Lazard projection of a given list of polynomials
  Usage
    projectionPhase(L)
  Inputs
    L:List
      of polynomials in a ring.
  Outputs
    S:List
      of lists of projection polynomials in increasing numbers of variables (starting with univariate polynomials and ending in the original list L).
    ordering:List
      of variables used in projections. The projection set of polynomials of in k variables will contain the first k variables of this list.
  Description
    Text
      The projection phase of the CAD is calculated. Given a list L of polynomials in $n$ variables (level $n$), the Lazard projection is applied recursively
      until one variable remains. At each step, the list of projection polynomials and the projected variable are stored, resulting in a final list of projection 
      polynomials from level 1 to level $n$, and the list of variables, ordered so that the first $k$ variables of the list are the variables of the polynomials
      at level $k$.
    Example
	  R=QQ[x1,x2,x3]
	  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
	  L={p0,p1,p2}
	  projectionPhase(L)
  SeeAlso
    gmodsHeuristic
    lazardProjection
///

doc ///
  Key
    (samplePoints, List)
    samplePoints
  Headline
    Computes a list of sample points in each cell that represent each open cell.
  Usage
    samplePoints(L)
  Inputs
    L:List
      nonempty, of polynomials in one variable.
  Outputs
    SP:List
      of points in QQ.
  Description
    Text
      Sample points are the representative points in each cell of the CAD. Such points are computed in the lifting phase, by isolating real 
      roots of the univariate polynomials obtained by substituting in sample points from lower levels.
      
      This method relies on the interval bisection method from realRootIsolation in the RealRoots package, which isolates the real roots within a specific half-open interval.
      If two intervals touch on a root, the interval bisection is run again with more precision until no intervals touch on a root.
      Once this is completed, it takes the midpoint of each interval as a sample point for each open region, along with points higher and lower than the largest and smallest,
      representing the first and last open cells.
    Example
      R=QQ[x]
      p0=x^2-1, p1=x^3-1;
      L1={p0,p1}
      samplePoints(L1)

      p2=5*x^3+1, p3=x^2-1, p4=1/2*x^5+3*x-1;
      L2={p2,p3,p4}
      samplePoints(L2)
  SeeAlso
///

doc ///
  Key
    (liftingPoint, List, MutableHashTable, List)
    liftingPoint
  Headline
    Given the projection phase of a CAD (S) and the variable ordering (ordering), this method returns an OpenCAD above the point (alpha) given.
  Usage
    liftingPoint(S,alpha,ordering)
  Inputs
    S:List
      of lists of RingElements, representing the projection polynomials of each level.
    alpha:MutableHashTable
      the point described using a hash table where the keys are RingElements (variables) and the values are sample points.
    ordering:List
      the variable ordering followed in the projection.
  Outputs
    LP:MutableHashTable
      describing an OpenCAD.
  Description
    Text
      Given the projection phase of a CAD (S), liftingPoint creates an Open Cylindrical Algebraic Decomposition, which breaks the space into cells where 
      the signs of the polynomials in each element of S are constant.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
      L={p0,p1,p2}
      alpha = new MutableHashTable
      alpha#x2 = -2, alpha#x3 = -3/32;
      (S,ordering) =  projectionPhase(L)
      LP = liftingPoint(S,alpha,ordering)
      hashify LP
  SeeAlso
    evalPolys
    samplePoints
///

doc ///
  Key
    (openCAD, List)
    openCAD
  Headline
    Given a list of polynomials, an open CAD of those polynomials is returned (main algorithm).
  Usage
    openCAD(L)
  Inputs
    L:List
      of polynomials all in the same ring.
  Outputs
    C:MutableHashTable
      describing an open CAD of the given list of polynomials.
  Description
    Text
      An open CAD is a mathematical object that decomposes the space into cells in which the given polynomials are sign invariant.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
      L={p0,p1,p2}
      openCAD(L)
      hashify openCAD(L)
      
      R=QQ[x1,x2]
      p0=x1-x2, p1=x1^3+x2^2;
      L={p0,p1}
      openCAD(L)
      hashify openCAD(L)
  SeeAlso
    projectionPhase
    liftingPoint
///

doc ///
  Key
    (positivePoint, List, MutableHashTable)
    positivePoint
  Headline
    Checks if there is a point in or above the given cell in which all the polynomials given in the list are strictly positive.
  Usage
    positivePoint(L,cell)
  Inputs
    L:List
      a list of polynomials.
    cell:MutableHashTable
      the cell of the CAD.
  Outputs
    PP:MutableHashTable
      describing a point in the cell (evaluations of all variables) where all polynomials in L are strictly positive (if one exists).
  Description
    Text
      Given the a list of polynomials and a cell of a CAD, this method checks if a point exists where all polynomials are strictly positive, or returns "no point exists" otherwise.
    Example
      R=QQ[x]
      p0=x^2-1, p1=x;
      L={p0,p1}
      C=openCAD(L);
      PP=positivePoint(L,C);
      hashify(PP)
  SeeAlso
    evalPolys
///

doc ///
  Key
    (findPositiveSolution, List)
    findPositiveSolution
  Headline
    Checks if there is a point in which all the polynomials given in the list are strictly positive
  Usage
    findPositiveSolution(L)
  Inputs
    L:List
      a list of polynomials.
  Outputs
    :Boolean
      saying whether the CAD of L of has a point where all of the polynomials in the list are strictly positive.
    :HashTable
      describing a point in the cell (evaluations of all variables) where all polynomials in L are strictly positive (if one exists).
    :List
      describing the polynomial(s) evaluated at this point (if the point exists).
  Description
    Text
      Given a list of polynomials L, this checks if the CAD of L contains a point where each of the polynomials in L are strictly positive.
    Example
      R=QQ[x]
      p0=x^2-1, p1=x;
      L={p0,p1}
      FS=findPositiveSolution(L)
  SeeAlso
    openCAD
    positivePoint
///

doc ///
  Key
    hashify
    (hashify, MutableHashTable)
    (hashify, HashTable)
    (hashify, List)
    (hashify, MutableList)
    (hashify, Thing)

  Headline
    Recursively turns MutableHashTables into equivalent HashTables.
  Usage
    hashify(MHT)
  Inputs
    M:MutableHashTable
      A mutable hash table.
    M:HashTable
      A hash table.
    M:List
      A list.
    M:MutableList
      A mutable list.
    M:Thing
      Any other object that isn't one of the ones listed above.
  Outputs
    H:Thing
      wherein any mutable hash tables are replaced with equivalent hash tables.
  Description
    Text
      This method takes a MutableHashTable, HashTable, List or MutableList and turns any MutableHashTables within into HashTables, leaving everything else the same.
    Example
      R=QQ[x1,x2];
      M = new MutableHashTable from {-1_QQ=>new MutableHashTable from {-5/2=>new MutableHashTable from {"point"=>new MutableHashTable from {x1=>-1_QQ, x2=>-5/2}}}};
      hashify M
  SeeAlso
    evalPolys
    liftingPoint
    openCAD
    positivePoint
    findPositiveSolution
///



-* Test section *-
TEST /// -* factors test *-
-- Test 0
  R=QQ[x1,x2,x3]
  p=x1^3*x2^3*x3-4*x1^2*x2^3*x3-x1^2*x2^2*x3^2+x1^2*x2^2*x3+4*x1*x2^3*x3+4*x1*x2^2*x3^2-4*x1*x2^2*x3-4*x2^2*x3^2+4*x2^2*x3
  F = factors(p)
  answer = {{x3, 1}, {x2, 2}, {x1 - 2, 2}, {x1*x2 - x3 + 1, 1}}
  assert(sort F === sort answer)
///

TEST /// -* factorsInList test *-
-- Test 1
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  F = factorsInList(L) 
  answer = {x2,x1,x1^2*x2+x3^3-x1*x3,x3,x2^2+1}
  assert(sort F === sort answer)
///

TEST /// -* evalPolys test *-
-- Test 2
  R=QQ[x1,x2,x3]
  p=x1^2*x2-x1*x3+x3^3
  alpha = new MutableHashTable;
  alpha#x1 = 1, alpha#x2 = 3;
  E = evalPolys(p,alpha)
  assert(E == 3-x3+x3^3)
///

TEST /// -* evalPolys test (List)*-
-- Test 3
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  alpha = new MutableHashTable
  alpha#x1 = 1, alpha#x2 = 3;
  E = evalPolys(L,alpha)
  assert(E == {3, 3-x3+x3^3, 9*x3+x3})
///

TEST /// -* leadCoeff test *-
-- Test 4
  R=QQ[x1,x2,x3]
  p=x1^2*x2-x1*x3+x3^3
  L = leadCoeff(p,x1)
  assert(leadCoeff(p,x1) == x2)
///

TEST /// -* gmodsHeuristic test *-
-- Test 5
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3, p3=-x1*x2;
  L={p0,p1,p2,p3}  
  assert(gmodsHeuristic(L,support(L)) == x1)
///

TEST /// -* lazardProjection test *-
-- Test 6
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  LP = lazardProjection(L,x1)
  assert(LP === {x2,x3,x2^2+1,4*x2*x3-1})
///

TEST /// -* projectionPhase test *-
-- Test 7
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  PP = projectionPhase(L)
  answerS = {{x2,x2^2+1}, {x2,x3,x2^2+1,4*x2*x3-1}, {x2,x1,x1^2*x2+x3^3-x1*x3,x3,x2^2+1}}
  answerordering = {x2, x3, x1}
  assert(PP == (answerS,answerordering))
///

TEST /// -* samplePoints test *-
-- Test 8
  R=QQ[x]
  p0=x^2-1, p1=x^3-1
  L={p0,p1}
  SP = samplePoints(L)
  assert(SP == {-3, -1/2, 2}) --this will be correct when the RealRoots update goes live
///

TEST /// -* liftingPoint test *-
-- Test 9
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1*x2+x3^2;
  L={p0,p1}
  (S,ordering) = projectionPhase(L)
  alpha = new MutableHashTable
  alpha#x3 = -1_QQ, alpha#x1 = 1_QQ;
  LP = liftingPoint(S,alpha,ordering)

  cellLevelThreeA = new MutableHashTable from {"point"=>new MutableHashTable from {x3=>-1_QQ, x1=>1_QQ, x2=>-3/4}}
  cellLevelThreeB = new MutableHashTable from {"point"=>new MutableHashTable from {x3=>-1_QQ, x1=>1_QQ, x2=>-5/2}  }
  cellLevelThreeC = new MutableHashTable from {"point"=>new MutableHashTable from {x3=>-1_QQ, x1=>1_QQ, x2=>1_QQ}}  

  cellLevelTwo = new MutableHashTable from {-3/4_QQ=>cellLevelThreeA, -5/2_QQ=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>new MutableHashTable from {x3=>-1_QQ, x1=>1_QQ}, "polynomials"=>{x2,1_QQ,x2+1}}

  assert(hashify(LP) === hashify(cellLevelTwo))
///

TEST /// -* openCAD test *-
-- Test 10
  R=QQ[x1,x2]
  p0=x1^2+x2, p1=x1^3*x2^2;
  L={p0,p1}
  C=openCAD(L)

  cellLevelThreeA = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>-1_QQ, x2=>-5/2}}
  cellLevelThreeB = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>-1_QQ, x2=>-3/4} }
  cellLevelThreeC = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>-1_QQ, x2=>1_QQ}}
  cellLevelThreeD = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>1_QQ, x2=>-5/2}}
  cellLevelThreeE = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>1_QQ, x2=>-3/4}}
  cellLevelThreeF = new MutableHashTable from {"point"=>new MutableHashTable from {x1=>1_QQ, x2=>1_QQ}}
  
  ptLevelTwoA = new MutableHashTable from {-5/2=>cellLevelThreeA, -3/4=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>new MutableHashTable from {x1=>-1_QQ}, "polynomials"=>{x2+1,x2,-1_QQ}}
  ptLevelTwoB = new MutableHashTable from {-5/2=>cellLevelThreeD, -3/4=>cellLevelThreeE, 1_QQ=>cellLevelThreeF, "point"=>new MutableHashTable from {x1=>1_QQ}, "polynomials"=>{x2+1,x2,1_QQ}}  
  ptLevelTwoC = new MutableHashTable
  
  cellLevelOne = new MutableHashTable from {-1_QQ=>ptLevelTwoA, 1_QQ=>ptLevelTwoB, "point"=>ptLevelTwoC, "polynomials"=>{x1}}
  
  assert(hashify cellLevelOne === hashify C)
  
///

TEST /// -* positivePoint test 1*-
-- Test 11
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3, p3=-x1*x2;
  L={p0,p1,p2,p3};
  C=openCAD(L)
  PP=positivePoint(L,C)
  assert(PP == "no point exists")
/// 
  
TEST /// -* positivePoint test 2*-
-- Test 12
  R=QQ[x]
  p0=x^2-1, p1=x;
  L={p0,p1};
  C=openCAD(L)
  PP=positivePoint(L,C)
  answer = new MutableHashTable from {x => 2_QQ}
  assert(hashify PP === hashify answer)
///

TEST /// -* findPositiveSolution test 1*-
-- Test 13
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  CAD = new HashTable from {x2=>1_QQ, x3=>5/4, x1=>1_QQ};
  assert(findPositiveSolution L === (true, CAD))
///

TEST /// -* findPositiveSolution test 2*-
-- Test 14
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3, p3=-x1*x2;
  L={p0,p1,p2,p3}
  assert(findPositiveSolution L === (false,"no point exists"))  
///

TEST /// -* findPositiveSolution test 3*-
-- Test 15
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3, p3=-x1*x2;
  L={p0,p1,p2,p3}
  assert(findPositiveSolution L === (false,"no point exists"))
/// 
  
TEST /// -* findPositiveSolution test 4*-
-- Test 16
  R=QQ[x]
  p0=x^2-1, p1=x;
  L={p0,p1}
  CAD = new HashTable from {x => 2_QQ};
  assert(findPositiveSolution L === (true, CAD))
///

TEST /// -* hashify test*-
-- Test 17
  R=QQ[x1,x2]
  MCell = new MutableHashTable from {-1_QQ=>new MutableHashTable from {-5/2=>new MutableHashTable from {"point"=>new MutableHashTable from {x1=>-1_QQ, x2=>-5/2}}}}
  HCell = new HashTable from {-1_QQ=>new HashTable from {-5/2=>new HashTable from {"point"=>new HashTable from {x1=>-1_QQ, x2=>-5/2}}}}
  assert(hashify MCell === HCell)
///

end--


