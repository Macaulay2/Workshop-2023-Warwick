-- To do

-- Note 21/03/2024 - Lots of updates. Testing examples for paper. Updated/checked commands, tests, docs and examples. 
-- Renamed leadCoefficientt to leadCoeff.
-- Updated a lot of commands and checked them, unifying naming.
-- samplePoint updated to only refind interval if two intervals actually touch on a root

-- Note 16/02/2024 Another fix to realRootIsolation to avoid it breaking when only roots are 0. 
-- Added RealRoots2 and imports from this while RealRoots proper needs fixing.
-- Also finally fixed liftingPoint test using thorough debugging using hash command.

-- Note 15/02/2024 Fixed RealRoots:-realRootIsolation, which should go into prod soon. Will need to update any checks relying on this now.

-- Note 29/01/2024: Fixed missing case of lazardProjection (was missing trailing coeffs), updated documentation.


-- Note 23/01/2024 - we need to tidy the documentation so each symbol is unique for each step (and is described the same)
-- e.g. L is always the initial list of polys p. 

-- Note 18/01/2024 - openCAD test is wrong, but original constructed hashTable also looks like it was even more wrong!
-- I think we should just work through an example slowly step-by-step comparing what we expect to get out
-- to what we actually receive, and use that to see where we're going wrong.

--Need to update this to do list.
--* Update examples, tests and documentation 
--* Create a "nice output" for openCAD - have a look at what Maple does
--* Extra: output descriptions of cells

--check all the "see also"s make sense and refer to all previous ones i guess!
--check samplePoints examples make sense - do them manually if you need to check.
--need to write documentation for hashify.
--positivePoint - output is a MHT - is that what we want?
--findSolution - example seems ok but check it!

newPackage(
    "CADecomposition",
    Version => "0.1",
    Date => "29/03/2023",
    Headline => "Cylindrical Algebraic Decomposition",
    Authors => {{ Name => "del Rio, T.", Email => "delriot@coventry.ac.uk", HomePage => "https://pureportal.coventry.ac.uk/en/persons/tereso-del-r%C3%ADo-almajano"},	{ Name => "Rahkooy, H.", Email => "rahkooy@maths.ox.ac.uk", HomePage => "https://people.maths.ox.ac.uk/rahkooy/"},	{ Name => "Lee, C.", Email => "cel34@bath.ac.uk", HomePage => "https://people.bath.ac.uk/cel34/"}},
    --PackageExports => {"Elimination", "RealRoots"}, --when RealRoots is updated, uncomment this.
    PackageExports => {"Elimination", "RealRoots2"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

--"A package can contain the code for many functions, only some of which should be made visible to the user.
--The function export allows one to specify which symbols are to be made visible."
--At the end, trim this down to only the ones useful for people using the package.
export {"factors",
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
"findSolution",
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
	-- try using lift command instead?
        for e in evaluations list e>0; --see if positive or not
        if all(evaluations, elem->(elem>0)) then (
          return cell#"point"
        )
    );
    return "no point exists"
)

-- Checks if there is a point in which all the polynomials given in the list are strictly positive
findSolution = method()
findSolution(List) := (L) -> (
    cad := openCAD(L);
    result := positivePoint(L, cad);
    if instance(result, HashTable)
    then (
      print(peek(result));
      print("There are solutions");
      return true)
    else (
      print("There is no solution");
      return false)
)

-- Turns MutableHashTables into HashTables
hashify = method()
hashify(MutableHashTable) := (H) -> (
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
      polynomial in a ring
  Outputs
    :List
      list of list pairs containing the polynomial's factors and their exponents.
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
     list of RingElements (polynomials in a ring).
  Outputs
    :List
      List containing the factors of each polynomial, without multiplicity.
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
      polynomial as a RingElement
    L:List
      list of polynomials as RingElements
    alpha:MutableHashTable
      point described using a mutable hash table where the keys are RingElements (variables in the ring)
  Outputs
    :RingElement
      RingElement describing the polynomial evaluated at the sample point.
    :List
      List of RingElements describing the polynomials evaluated at the sample point.
  Description
    Text
      Given the polynomial (p) or list of polynomials (L) and sample point (alpha), evalPolys evaluates the 
      polynomial(s) at the sample point and returns the evaluated polynomial(s). 
      This is used in the lifting phase of the CAD, where a polynomial in $k$ variables is evaluated at a point 
      $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return a univariate polynomial in $\mathbb{R}[x_k]$.
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
      a polynomial in the ring
    v:RingElement
      a variable in the ring
  Outputs
    :RingElement
      the leading coefficient of $p$ with respect to the variable $v$.
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
      of polynomials in several variables
    variables:List
      of variables in the polynomials provided
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
      of polynomials all in the same ring
    v:RingElement
      a variable in the ring
  Outputs
    :List
      list of projected polynomials not involving $v$
  Description
    Text
      Lazard projection is an operation that takes a variable $v$ and a set $L$ of polynomials in $n$ variables, and returns a set of polynomials 
      in the remaining $n-1$ variables, representing the significant points of the polynomials.
      This is used in the projection phase of Cylindrical Algebraic Decomposition, and consists of the leading and trailing coefficients of the given 
      polynomials w.r.t $v$, the discriminants of the polynomials w.r.t $v$ and the resultants between each pair of polynomials 
      w.r.t $v$. For openCAD, the trailing coefficients are not needed.
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
      of polynomials in a ring
  Outputs
    S:List
      of lists of projection polynomials in increasing numbers of variables (starting with univariate polynomials and ending in the original list $L$).
    ordering:List
      of variables used in projections. The projection set of polynomials of in $k$ variables will contain the first $k$ variables of this list.
  Description
    Text
      The projection phase of the CAD is calculated. Given a list $L$ of polynomials in $n$ variables (level $n$), the Lazard projection is applied recursively
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
      nonempty, of polynomials in one variable
  Outputs
    SP:List
      list of points in QQ
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
      list of lists of RingElements
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables) and the values are sample points.
    ordering:List
      variable ordering followed in the projection
  Outputs
    LP:MutableHashTable
      MutableHashTable describing an OpenCAD
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
      of polynomials all in the same ring
  Outputs
    C:MutableHashTable
      describing an open CAD of the given list of polynomials
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
    Checks if there is a point in or above the given cell in which all the polynomials given in the list are strictly positive
  Usage
    positivePoint(L,cell)
  Inputs
    L:List
      list of polynomials
    cell:MutableHashTable
      cell of the CAD
  Outputs
    PP:MutableHashTable
      MutableHashTable describing a point in the cell (evaluations of all variables) where all polynomials in L are strictly positive
  Description
    Text
      Given the a list of polynomials and a cell of a CAD, it checks if a point exists where all polynomials are strictly positive, or returns "no point exists" otherwise.
    Example
      R=QQ[x]
      p0=x^2-1
      p1=x
      L={p0,p1}
      C=openCAD(L)
      PP=positivePoint(L,C)
  SeeAlso
    evalPolys
///

doc ///
  Key
    (findSolution, List)
    findSolution
  Headline
    Checks if there is a point in which all the polynomials given in the list are strictly positive
  Usage
    findSolution(L)
  Inputs
    L:List
      list of polynomials
  Outputs
    :Boolean
      Whether the CAD of L of has a point where all of the polynomials in the list are strictly positive
  Description
    Text
      Given a list of polynomials L, this checks if the CAD of L contains a point where each of the polynomials in L are strictly positive.
    Example
      R=QQ[x]
      p0=x^2-1
      p1=x
      L={p0,p1}
      FS=findSolution(L)
  SeeAlso
    openCAD
    positivePoint
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
  assert(LP === {x3,x2^2+1,x2,4*x2*x3-1})
///

TEST /// -* projectionPhase test *-
-- Test 7
  R=QQ[x1,x2,x3]
  p0=x1*x2, p1=x1^2*x2-x1*x3+x3^3, p2=x2^2*x3+x3;
  L={p0,p1,p2}
  PP = projectionPhase(L)
  answerS = {{x2^2+1,x2}, {x3,x2^2+1,x2,4*x2*x3-1}, {x1*x2,x1^2*x2+x3^3-x1*x3,x2^2*x3+x3}}
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
  alpha#x3 = -1_QQ, alpha#x2 = 1_QQ;
  LP = liftingPoint(S,alpha,ordering)

  ptLevelThreeA = new MutableHashTable from {x3=>-1_QQ, x2=>1_QQ, x1=>-3/4}
  ptLevelThreeB = new MutableHashTable from {x3=>-1_QQ, x2=>1_QQ, x1=>-5/2}  
  ptLevelThreeC = new MutableHashTable from {x3=>-1_QQ, x2=>1_QQ, x1=>1_QQ}   
  ptLevelTwo = new MutableHashTable from {x3=>-1_QQ, x2=>1_QQ}
  cellLevelThreeA = new MutableHashTable from {"point"=>ptLevelThreeA}
  cellLevelThreeB = new MutableHashTable from {"point"=>ptLevelThreeB}
  cellLevelThreeC = new MutableHashTable from {"point"=>ptLevelThreeC}  
  cellLevelTwo = new MutableHashTable from {-3/4_QQ=>cellLevelThreeA, -5/2_QQ=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>ptLevelTwo, "polynomials"=>{x1,x1+1}}

  assert(hashify(LP) === hashify(cellLevelTwo))
///

TEST /// -* openCAD test *-
-- Test 10
  R=QQ[x1,x2]
  p0=x1^2+x2, p1=x1^3*x2^2;
  L={p0,p1}
  C=openCAD(L)

  ptLevelFourA = new MutableHashTable from {x1=>-1_QQ, x2=>-5/2}
  ptLevelFourB = new MutableHashTable from {x1=>-1_QQ, x2=>-3/4} 
  ptLevelFourC = new MutableHashTable from {x1=>-1_QQ, x2=>1_QQ}
  ptLevelFourD = new MutableHashTable from {x1=>1_QQ, x2=>-5/2}
  ptLevelFourE = new MutableHashTable from {x1=>1_QQ, x2=>-3/4}
  ptLevelFourF = new MutableHashTable from {x1=>1_QQ, x2=>1_QQ}
  
  cellLevelThreeA = new MutableHashTable from {"point"=>ptLevelFourA}
  cellLevelThreeB = new MutableHashTable from {"point"=>ptLevelFourB}
  cellLevelThreeC = new MutableHashTable from {"point"=>ptLevelFourC}
  cellLevelThreeD = new MutableHashTable from {"point"=>ptLevelFourD}
  cellLevelThreeE = new MutableHashTable from {"point"=>ptLevelFourE}
  cellLevelThreeF = new MutableHashTable from {"point"=>ptLevelFourF}

  ptLevelThreeA = new MutableHashTable from {x1=>-1_QQ}
  ptLevelThreeB = new MutableHashTable from {x1=>1_QQ}
  
  ptLevelTwoA = new MutableHashTable from {-5/2=>cellLevelThreeA, -3/4=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>ptLevelThreeA, "polynomials"=>{x2+1,-x2^2}}
  ptLevelTwoB = new MutableHashTable from {-5/2=>cellLevelThreeD, -3/4=>cellLevelThreeE, 1_QQ=>cellLevelThreeF, "point"=>ptLevelThreeB, "polynomials"=>{x2+1,x2^2}}  
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

TEST /// -* findSolution test 1*-
-- Test 13
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,p2}
  assert(findSolution(L) == true)
///

TEST /// -* findSolution test 2*-
-- Test 14
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  p3=-x1*x2
  L={p0,p1,p2,p3}
  assert(findSolution(L) == false)
///

TEST /// -* findSolution test 3*-
-- Test 15
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  p3=-x1*x2
  L={p0,p1,p2,p3}
  FS=findSolution(L)
  assert(FS == false)
/// 
  
TEST /// -* findSolution test 4*-
-- Test 16
  R=QQ[x]
  p0=x^2-1
  p1=x
  L={p0,p1}
  FS=findSolution(L)
  assert(FS == true)
///




end--

-* Development section *-
restart
debug needsPackage "CADecomposition" --load package
--needsPackage "CADecomposition"
check "CADecomposition" --run tests

restart
uninstallPackage "CADecomposition"
restart
installPackage("CADecomposition",IgnoreExampleErrors=>true) --load and install a package and its documentation
installPackage("CADecomposition")
uninstallPackage "RealRoots"
installPackage "RealRoots2" --while we wait for RealRoots to update, this is the fixed version
--installPackage "CADecomposition" --load and install a package and its documentation
viewHelp "CADecomposition"
--if this does not load properly, html files should now be created in
--home\[name]\.Macaulay2\local\share\doc\Macaulay2\CADecomposition\html

--====================

    --L1 = {max ourRoots_0)-1}|L1|{ourRoots_(#ourRoots-1)_1+1};
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,-p2}
  assert(findSolution(L) == true)

  H = openCAD {p0,p1,-p2}
  keys H
  peek oo
  peek H#(-2_QQ)
  
R=QQ[x1,x2]
L={x1*x2}
openCAD(L)

--==============================

--EXAMPLE TO RUN THROUGH FOR PAPER--
R=QQ[x1,x2]
p1:=x1^2+x2^2-1
p2:=x1^3-x2^2
L={p1,p2}

findSolution(L);


alpha = new MutableHashTable -- this is a test, this a solution!
alpha#x1 = 2
alpha#x2 = 1
evalPolys(L,alpha)

factors(p1)
factors(p2)
support(L)
factorsInList(L)

GML:=gmodsHeuristic(L,support(L))

leadCoeff(p1,GML)
leadCoeff p2,GML)

lazardProjection(L,GML)

projectionPhase(L);

samplePoints(lazardProjection(L,GML));

--==========================================================

 R=QQ[x]
  f=x^2-1
  g=x^3-1
  L1={f,g}
  S = samplePoints(L1)

--x^4+x^3-x-1

--============================

R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1*x2+x3^2
  L={p0,p1}
  (P,ord) = projectionPhase(L)
  pts = new MutableHashTable
  pts#x1 = -1
  pts#x2 = 3
  --ord = {x2,x1,x3}
  LP = liftingPoint(P,pts,ord)

--========================

--big example: intersecting sphere. This is 3-dim and takes about 58 seconds.
R = QQ[x1,x2,x3]
L = {(x1-1)^2+(x2-1)^2+(x3-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2-2^2}
timing openCAD(L)

var = gmodsHeuristic(L,support(L))
lazardProjection(L,var)
(S,ordering) = projectionPhase(L)

samplePoints(S#0) --this is one of the crazy parts
