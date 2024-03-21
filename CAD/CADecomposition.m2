-- To do

-- Note 16/02/2023 Another fix to realRootIsolation to avoid it breaking when only roots are 0. 
-- Added RealRoots2 and imports from this while RealRoots proper needs fixing.
-- Also finally fixed liftingPoint test using thorough debugging using hash command.

-- Note 15/02/2023 Fixed RealRoots:-realRootIsolation, which should go into prod soon. Will need to update any checks relying on this now.

-- Note 29/01/2023: Fixed missing case of lazardProjection (was missing trailing coeffs), updated documentation.


-- Note 23/01/2023 - we need to tidy the documentation so each symbol is unique for each step (and is described the same)
-- e.g. L is always the initial list of polys p. 

-- Note 18/01/2023 - openCAD test is wrong, but original constructed hashTable also looks like it was even more wrong!
-- I think we should just work through an example slowly step-by-step comparing what we expect to get out
-- to what we actually receive, and use that to see where we're going wrong.



--LEGACY: Check if these are still valid or not:
--  Issue with positivePoint and findSolution - don't load properly, giving wrong output
--  Trying to lift to QQ in evalPoly where possible, but this seems to break many other checks.

--Need to update this to do list.
--* Update examples, tests and documentation 
--*  * (tests #2,3,5,7,9,10 failing) (evalPolys, evalPolys (List), gmodsHeuristic, projectionPhase, liftingPoint (the big one), openCAD smaller)
--* Make sure realRootIsolation works as expected or that we can manipulate it into doing what we want (it has
--  an issue where e.g. x1 would give isolation {-1,1} but -2*x1 would give isolation {1,-1} (interval switches here).
--  What we need to do here is to make a workaround that forces it the right way round (e.g. sets the lower one as the
--  first bound and the second as the lower), so we can correctly make the "-infinity to first root"
--  and the "last root to infinity" intervals (but we need to find and get the smallest and the largest bounds first!)
--* Create a "nice output" for openCAD - have a look at what Maple does
--* Extra: output descriptions of cells

--find out what "ourRoots" outputs.

--evalPolys - need to get it working for Lists too.
--is gmodsHeuristic sorted now? check the example works like it should etc.
--check lazardProjection example makes sense - do it manually too (might as well write that up if i do)
--check all the "see also"s make sense and refer to all previous ones i guess!
--projectionPhase is ok i think?
--check samplePoints examples make sense - do them manually if you need to check.
--liftingPoint example is broken.

--is latterContainsFormer still used? If not we can remove it. If so, check it still works properly.
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
"leadCoefficientt",
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
  L := p//factor//toList/toList
  -- print L
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
    L0 := apply(L, p -> factors(p)); --calls 'factors' on each element of L
    -- print("Unflattend list of factors:", L0);
    L1 := flatten(L0); --flattens these to a list containing listed pairs (factors and multiplicities)
    L2 := L1/first//unique; --take the first element of each of these lists and keeps unique ones, only returning the unique factors of all the polynomials in one list.
    L3 := select(L2, p -> #support p>0 ) --keeps only nonconstant/nonempty  elements of the list
)



-- Evaluates the given RingElement or List of RingElements at a point given by a MutableHashTable.
evalPolys = method()
evalPolys(RingElement,MutableHashTable) := (p, alpha) -> (
        for k in keys(alpha) do(
          -- print("variable", k);
          p=sub(p, {k => alpha#k});
        );
	if liftable(p,QQ) then p = lift(p,QQ);
-- currently breaks 'support' - need to add a case where if element is in QQ then return {}?
        p
      )
evalPolys(List,MutableHashTable) := (S, alpha) -> (
  S1 := for p in S list
    evalPolys(p,alpha);
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
gmodsHeuristic(List, List) := (L, variables) -> (
  gmodsVar := variables_0;
  minGmods := sum(for p in L list degree(variables_0, p));
  for var in variables do (
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
  L0 := select(L, p -> not member(v,support(p))); --polynomials not relying on v
  L = select(L, p -> member(v,support(p))); --remove polynomials p not relying on v 
  -- as these would create redundant calculations (resultants would be a power of p,
  -- discriminants and leading coefficient would be 0 and trailing coefficient would be p
  -- so we will just slot these back in later)
  --print "L";print L;
  -- "return the parts of each poly p in L that rely on v"
        L1 := for p in L list leadCoefficientt(p,v); --lead coefficients
        L2 := for p in L list p-v*contract(v,p); --trailing coefficients
	L3 := for p in L list discriminant(p,v); --discriminants
	L4 := for p in subsets(L,2) list resultant(p_0,p_1,v); --resultants
        --print "L0,L1,L2,L3,L4";print L0;print L1;print L2;print L3;print L4;
	factorsInList(L0|L1|L2|L3|L4) -- put these back together as one list, but as factors (squarefree).
	)

-- Creates a full Lazard projection
projectionPhase = method()
projectionPhase(List) := (L) -> (
    -- List is list of multivariate polynomials
    S := {L};
    variables := support(L); --initial variables, the ones chosen already will be dropped
    --print variables;
    ordering := {}; -- this will contain the variable ordering chosen
    --print ordering;
    while length(variables) > 1 do (
      -- print(L);
    --   var := gmodsHeuristic(support(L)); (Line commnented out because the following felt more reasonable, if no errors were created remove this line)
      var := gmodsHeuristic(L, variables);
      --print var;
      L = lazardProjection(L, var);
      variables = select(variables,n -> n != var); -- variable chosen is dropped
      S = prepend(L, S); --
      --print S;
      ordering = prepend(var, ordering);
      --print ordering;
      );
    ordering = prepend(variables_0, ordering); -- the variable left is added
    --print "S, ordering";
    --print S; print ordering;
    (S, ordering)
    )

-- Given a nonempty list of univariate polynomials, samplePoints prduces sample points for the cells (seperating the roots)
samplePoints = method()
samplePoints(List) := (L) -> (
    -- if L=={} then error "Error: Expected non-empty list";
    -- set up A, monoid on single variable
    A := QQ(monoid[support(L)]);
    -- put product of polys in L inside ring A.
    h:=sub(product L, A);
    print("List of Pols and their product:"); print L; print h;
    -- set initial interval size as 1 for isolating intervals
    intervalSize := 1;
    --call RealRoots:realRootIsolation (isolates real solutions of h in intervals of length at most 1)
    ourRoots := realRootIsolation(h,intervalSize); -- when RealRoots is evaluating h they get an element of R, not a number. Returns interval.
    print "root isolating intervals"; print ourRoots;
    -- if no roots, set L1 to empty list.
    if length(ourRoots)==0 then (
        L1 := {};
      )
      else (
    -- if two consecutive intervals have a shared start/end point that is a root then refine intervals:
      for i from 0 to #ourRoots-2 do (
      -- print("Roots", ourRoots);
        while (ourRoots_i_1)==(ourRoots_(i+1)_0) do (
            --check this! bug with package might mean we have to check if both sides have any elements in common at all!
          intervalSize = intervalSize/2;
          ourRoots = realRootIsolation(h,intervalSize);
        );
      );
    print "ourRoots refined"; print ourRoots;
    -- Find the mid-points between intervals as cell witnesses:
    L1 = for i from 1 to #ourRoots-1 list (ourRoots_(i-1)_1+ourRoots_i_0)/2;
    print "Mid Points:"; print L1;
    -- Add the beginning of the first interval and the end of the last interval to the list, but each of which -+1 in order to avoid them being a root:
    -- (putting all roots into QQ - get +-1 in ZZ if one root
    L1 = {((min (flatten ourRoots))-1)_QQ}|L1|{((max (flatten ourRoots))+1)_QQ};
    print "Mid Points and first and last:"; print L1;
    );
    L1
  )

-- Given the list of lists of polynomials that the projection returns creates a CAD in a tree-like hash structure
-- starting from the point p given. i is the level and could be deduced from p but it is sent to ease understanding
liftingPoint = method()
liftingPoint(List, MutableHashTable, List) := (S, p, ordering) -> (
    -- List (S) is a list of lists of polynomials, the first list of polys with i+1 variables (up to n variables, where n is the number of variables in the initial polynomials)
    -- CHECK: the list of projections? I.e. n vars, n-1 vars, ..., 2 vars, 1 var? So i different lists?
    -- HashTable (p) is a point in i variables
    -- List (ordering) is the variable ordering followed in the projection
    
    print "S, p, ordering"; -- [test for understanding]
    print S; -- [test for understanding]
    print p; -- [test for understanding]
    print ordering;  -- [test for understanding]


    cell := new MutableHashTable;
    cell#"point" = p;
    i := #keys(p); --number of variables that have been assigned
    print "i"; -- [test for understanding]
    print i; -- [test for understanding]
    -- we check if all the variables have been given a value already
    if i >= length(S) then return cell; -- if so just return an empty MutableHashTable
    U := evalPolys(S_i, p); -- evaluating the polys in i+1 vars at point p (so U should be a set of univariate polynomials)
    cell#"polynomials"=U;
    print "U, S_i, p"; -- [test for understanding]
    print U; -- [test for understanding]
    print S_i; -- [test for understanding]
    print p; -- [test for understanding]

    -- I want this to ensure that values are returned as values, but including it also breaks tests #12,14,15,16,17.
    --if liftable(U,QQ) then U = lift(p,QQ); -- if a value, return as a value.
    -- "U = lift(p,QQ)" may have just been a typo, see if it helps!
    
    
    
    --Check in case U is not univariate.
    if #support(U) > 1 then error ("Expected list of polynomials to have a single variable as support. The value of U is " | toString(U));
    -- v := (support(U))_0;
    v := ordering_i;
    print "v"; -- [test for understanding]
    print v; -- [test for understanding]
    newSamplePoints := samplePoints(U);
    for samplePoint in newSamplePoints do (
        pNew := copy p;
        pNew#v = samplePoint;
        print "pNew#v (samplePoint)"; -- [test for understanding]
        print pNew#v; -- [test for understanding]
        cell#samplePoint = liftingPoint(S, pNew, ordering);
	--have to keep S, not SNew, as i increases, but #(SNew) would decrease.
	--either keep this as S or ise SNew and replace i with 0.
        );
    --print cell
    --DF:=ASDF
    cell
    )

--cell#samplePoint should be in SNew? No, we can probably remove this line.

--liftingPoint effectively makes a MHT for (i+1)th variable w.r.t. ordering, we'll call this x_(i+1), with
-- "point":        p, the values for the "first" i variables (w.r.t ordering)
-- "polynomials":  these values substituted into the projection polynomials for level i+1 
--                 (polys with i+1 variables), making a set of univariate polys in x_(i+1) (we call this L)
-- [numeric]:      each of the sample points of L. Inside this is a new, more detailed MHT for the
--                 "first" i+1 variables (i.e. the values from p along with the new sample point

-- get the order the right way round when explaining it, are the proj polys starting with all n vars, then
-- decreasing by one with each set down to 1, and does ordering reflect this?

-- this starts at the "top" level (get level numbers right way round), with the "most important variable"
-- (check this too, is the most important one projected away first?)

-- check how it works with an example. You would expect:
-- topmost layer: point is empty, polynomials are the original 


-- Does the open CAD
openCAD = method()
openCAD(List) := (L) -> (
  (S, ordering) := projectionPhase(L);
  p := new MutableHashTable;
  liftingPoint(S, p, ordering)
)

-- Checks if there is a point in or above the given cell in which all the polynomials given in the list are strictly positive
positivePoint = method()
positivePoint(List, MutableHashTable) := (L, cell) -> (
    if length(keys(cell#"point"))!=length(support(L)) then (
        for key in keys(cell) do(
            -- if the key is not "points" or "polynomials"
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
	evaluations = for e in evaluations list value(toString(e)); --elements in list were in R and not treated as numbers, this fixes that.
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
    factors
///

doc ///
  Key
    evalPolys
    (evalPolys, RingElement, MutableHashTable)
    (evalPolys, List, MutableHashTable)
  Headline
    Evaluates the given polynomial or list of polynomials with respect to the given sample points.
  Usage
    evalPolys(p,alpha)
    evalPolys(L,alpha)
  Inputs
    p:RingElement
      polynomial as a RingElement
    L:List
      List of polynomials as RingElements
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :RingElement
      RingElement describing the polynomial evaluated at the sample point.
    :List
      List of RingElements describing the polynomials evaluated at the sample point.
  Description
    Text
      Given the polynomial (p) or list of polynomials (L) and sample point (alpha), evalPolyst evaluates the polynomial(s) at the sample point and returns the evaluated polynomial(s). 
      This is used in the lifting phase of the CAD, where a polynomial in $k$ variables is evaluated at a point 
      $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return a univariate polynomial in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  p0=x1^2*x0-2*x3*x2
	  evalPolys(p0,alpha)
	  alpha1 := copy alpha
	  alpha1#x3 = -2
	  evalPolys(p0,alpha1)
          p1=x0*(x1-1)*(x2-2)*(x3-3)
    	  L = {p0,p1}
	  evalPolys(L,alpha)
	  evalPolys(L,alpha1)
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
      RingElement giving the next variable
  Description
    Text
      Given a list (L) of polynomials in one or more variables, returns the variable with the lowest degree in the product of the given polynomials. In case of tie, the 
      variable that appears earlier in support(L) is returned. This heuristic is motivated by the complexity analysis of CAD. Further information regarding this 
      heuristic can be found in "https://doi.org/10.1007/978-3-031-14788-3_17".
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      p3=-x1*x2
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
      Lazard projection is an operation that takes a variable $v$ set of polynomials in n variables and returns a set of polynomials without that variable. 
      It is used in the projection phase of Cylindrical Algebraic Decomposition and it consists of the leading and trailing coefficients of the given 
      polynomials with respect to (w.r.t) $v$, the discriminant of the given polynomials w.r.t $v$ and the resultant between any pair of given polynomials 
      w.r.t $v$. For openCAD, the trailing coefficients are not needed.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      L2 = lazardProjection(L,x1)
  SeeAlso
    leadCoefficientt
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
      of polynomials
  Outputs
    :List
      of lists of projection polynomials in decreasing numbers of variables
  Description
    Text
      Given a list (L) of polynomials or a list of lists of polynomials, these are stored, then a variable is selected using gmods, and the Lazard 
      projection is done on the polynomials. This new list in one fewer variables is also stored, and the process is repeated on this new list 
      until only polynomials in one variable remain.
    Example
      R=QQ[x]
	  R=QQ[x1,x2,x3]
	  f0=x1*x2
	  f1=x1^2*x2-x1*x3+x3^3
	  f2=x2^2*x3+x3
	  L={f0,f1,f2}
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
    Computes a list of sample points in each cell that isolate the roots
  Usage
    samplePoints(L)
  Inputs
    L:List
      nonempty, of polynomials in one variable
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
    (liftingPoint, List, MutableHashTable, List)
    liftingPoint
  Headline
    Given the projection phase of a CAD (S) and the variable ordering (ordering) it returns an OpenCAD above the point (p) given.
  Usage
    liftingPoint(S,p,ordering)
  Inputs
    S:List
      list of lists of RingElements
    p:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
    ordering:List
      variable ordering followed in the projection
  Outputs
    :MutableHashTable
      MutableHashTable describing an OpenCAD
  Description
    Text
      Given the projection phase of a CAD (S) it creates an Open Cylindrical Algebraic Decomposition. It basically breaks the space into cells where the sign of the 
      RingElements in S_(-1) are constant.
    Example
      R=QQ[x1,x2,x3]
      p0=x1*x2
      p1=x1^2*x2-x1*x3+x3^3
      p2=x2^2*x3+x3
      L={p0,p1,p2}
      pts = new MutableHashTable
      pts#x2 = -2
      pts#x3 = -3/32
      (S,ordering) =  projectionPhase(L)
      LP = liftingPoint(S,pts,ordering)
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
      hashify openCAD(L)
      
      R=QQ[x1,x2]
      p0=x1-x2
      p1=x1^3+x2^2
      L={p0,p1}
      S := projectionPhase(L);
      print S
      --p := new MutableHashTable;
      --liftingPoint(S,p)
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
    :MutableHashTable
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
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,p2}
  F = factorsInList(L) 
  answer = {x2,x1,x1^2*x2+x3^3-x1*x3,x3,x2^2+1}
  assert(sort F === sort answer)
///

TEST /// -* evalPolys test *-
-- Test 2
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  p = new MutableHashTable
  p#x1 = 1
  p#x2 = 3
  E = evalPolys(f1,p)
  answer = 3-x3+x3^3
  assert(E == answer)
///

TEST /// -* evalPolys test (List)*-
-- Test 3
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  p = new MutableHashTable
  p#x1 = 1
  p#x2 = 3
  E = evalPolys(L,p)
  answer = {3, 3-x3+x3^3, 9*x3+x3}
  assert(E == answer)
///

TEST /// -* leadCoefficientt test *-
-- Test 4
  R=QQ[x1,x2,x3]
  p=x1^2*x2-x1*x3+x3^3
  L = leadCoefficientt(p,x1)
  answer = x2
  assert(L == answer)
///

TEST /// -* gmodsHeuristic test *-
-- Test 5
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  p3=-x1*x2
  L={p0,p1,p2,p3}  
  assert(gmodsHeuristic(L,support(L)) == x1)
///

TEST /// -* lazardProjection test *-
-- Test 6
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
-- Test 7
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L={f0,f1,f2}
  P = projectionPhase(L)
  answerS = {{x2^2+1,x2}, {x3,x2^2+1,x2,4*x2*x3-1}, {x1*x2,x1^2*x2+x3^3-x1*x3,x2^2*x3+x3}}
  answerordering = {x2, x3, x1}
  assert(P == (answerS,answerordering))
///

TEST /// -* samplePoints test *-
-- Test 8
  R=QQ[x]
  f=x^2-1
  g=x^3-1
  L1={f,g}
  S = samplePoints(L1)
  answer = {-3, -1/2, 2} --this will be correct when the RealRoots update goes live
  assert(S == answer)
///

TEST /// -* liftingPoint test *-
-- Test 9
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1*x2+x3^2
  L={p0,p1}
  (P,ord) = projectionPhase(L)
  print P
  print ord
  pts = new MutableHashTable
  pts#x3 = -1
  pts#x2 = 3
  --ord = {x2,x1,x3}
  LP = liftingPoint(P,pts,ord)

  pLevelThreeA = new MutableHashTable from {x3=>-1, x2=>3, x1=>-3/2}
  pLevelThreeB = new MutableHashTable from {x3=>-1, x2=>3, x1=>-1/4}  
  pLevelThreeC = new MutableHashTable from {x3=>-1, x2=>3, x1=>1_QQ}   
  pLevelTwo = new MutableHashTable from {x3=>-1, x2=>3}
  
  cellLevelThreeA = new MutableHashTable from {"point"=>pLevelThreeA}
  cellLevelThreeB = new MutableHashTable from {"point"=>pLevelThreeB}
  cellLevelThreeC = new MutableHashTable from {"point"=>pLevelThreeC}  

  cellLevelTwo = new MutableHashTable from {-3/2_QQ=>cellLevelThreeA, -1/4_QQ=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>pLevelTwo, "polynomials"=>{3*x1,3*x1+1}}

  assert(hashify(LP) === hashify(cellLevelTwo))
///

TEST /// -* openCAD test smaller *-
-- Test 10
  R=QQ[x1,x2]
  p0=x1^2+x2
  p1=x1^3*x2^2
  L={p0,p1}
  C=openCAD(L)
  peek C
  
  gmodsHeuristic(L,support(L))
  
  hashify C

  pLevelFourA = new MutableHashTable from {x1=>-1_QQ, x2=>-5/2}
  pLevelFourB = new MutableHashTable from {x1=>-1_QQ, x2=>-3/4} 
  pLevelFourC = new MutableHashTable from {x1=>-1_QQ, x2=>1_QQ}
  pLevelFourD = new MutableHashTable from {x1=>1_QQ, x2=>-5/2}
  pLevelFourE = new MutableHashTable from {x1=>1_QQ, x2=>-3/4}
  pLevelFourF = new MutableHashTable from {x1=>1_QQ, x2=>1_QQ}
  
  cellLevelThreeA = new MutableHashTable from {"point"=>pLevelFourA}
  cellLevelThreeB = new MutableHashTable from {"point"=>pLevelFourB}
  cellLevelThreeC = new MutableHashTable from {"point"=>pLevelFourC}
  cellLevelThreeD = new MutableHashTable from {"point"=>pLevelFourD}
  cellLevelThreeE = new MutableHashTable from {"point"=>pLevelFourE}
  cellLevelThreeF = new MutableHashTable from {"point"=>pLevelFourF}

  pLevelThreeA = new MutableHashTable from {x1=>-1_QQ}
  pLevelThreeB = new MutableHashTable from {x1=>1_QQ}
  
  pLevelTwoA = new MutableHashTable from {-5/2=>cellLevelThreeA, -3/4=>cellLevelThreeB, 1_QQ=>cellLevelThreeC, "point"=>pLevelThreeA, "polynomials"=>{x2+1,-x2^2}}
  pLevelTwoB = new MutableHashTable from {-5/2=>cellLevelThreeD, -3/4=>cellLevelThreeE, 1_QQ=>cellLevelThreeF, "point"=>pLevelThreeB, "polynomials"=>{x2+1,x2^2}}  
  pLevelTwoC = new MutableHashTable
  
  cellLevelOne = new MutableHashTable from {-1_QQ=>pLevelTwoA, 1_QQ=>pLevelTwoB, "point"=>pLevelTwoC, "polynomials"=>{x1}}
  
  assert(hashify cellLevelOne === hashify C)
///

TEST /// -* positivePoint test 1*-
-- Test 11
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  p3=-x1*x2
  L={p0,p1,p2,p3}
  C=openCAD(L)
  PP=positivePoint(L,C)
  PP
  assert(PP == "no point exists")
/// 
  
TEST /// -* positivePoint test 2*-
-- Test 12
  R=QQ[x]
  p0=x^2-1
  p1=x
  L={p0,p1}
  C=openCAD(L)
  PP=positivePoint(L,C)
  answer = new MutableHashTable from {
      x => 2_QQ}
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

leadCoefficientt(p1,GML)
leadCoefficientt(p2,GML)

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
