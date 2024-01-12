-- To do

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

--tests:
--gmodsHeuristic test (Test 5) fails - no method for applying to a list.
--projectionPhase test (Test 7) fails - no method for applying sort to these - check what changed.
--samplePoints test (Test 8) is fine but check it makes sense if things have changed!
--liftingPoint test (Test 9) is a complete mess - need to sit down and think about it in detail.
--same with openCAD test (Test 10)
--findSolution tests - maybe make all of the same form: FS = findSolution, then assert FS is true/false.

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
"gmodsHeuristic",
"lazardProjection",
"projectionPhase",
"samplePoints",
"liftingPoint",
"openCAD",
"latterContainsFormer",
"positivePoint",
"findSolution"
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
    L0 := apply(L, p -> factors(p));
    -- print("Unflattend list of factors:", L0);
    L1 := flatten(L0);
    L2 := L1/first//unique;
    L3 := select(L2, p -> #support p>0 )
)



-- Evaluates the given RingElement or List of RingElement in a point given by a MutableHashTable.
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
  L0 := select(L, p -> not member(v,support(p))); --trailing coefficients
  L = select(L, p -> member(v,support(p)));
  L1 := for p in L list leadCoefficientt(p,v); --lead coefficients
	L2 := for p in L list discriminant(p,v); --discriminants
	L3 := for p in subsets(L,2) list resultant(p_0,p_1,v); --resultants
	factorsInList(L0|L1|L2|L3)
	)

-- Creates a full Lazard projection
projectionPhase = method()
projectionPhase(List) := (L) -> (
    -- List is list of multivariate polynomials
    S := {L};
    variables := support(L); --initial variables, the ones chosen already will be dropped
    ordering := {}; -- this will contain the variable ordering chosen
    while length(variables) > 1 do (
      -- print(L);
    --   var := gmodsHeuristic(support(L)); (Line commnented out because the following felt more reasonable, if no errors were created remove this line)
      var := gmodsHeuristic(L, variables);
      L = lazardProjection(L, var);
      variables = select(variables,n -> n != var); -- variable chosen is dropped
      S = prepend(L, S);
      ordering = prepend(var, ordering);
      );
    ordering = prepend(variables_0, ordering); -- the variable left is added
    (S, ordering)
    )

-- Given a nonempty list of univariate polynomials, samplePoints prduces sample points for the cells (seperating the roots)
samplePoints = method()
samplePoints(List) := (L) -> (
    -- if L=={} then error "Error: Expected non-empty list";
    A := QQ(monoid[support(L)]);
    h:=sub(product L, A);
    -- print("List of Pols:"); print L;
    -- print h;
    intervalSize := 1;
    ourRoots := realRootIsolation(h,intervalSize); -- when RealRoots is evaluating h they get an element of R, not a number. Returns interval.
    -- print "root isolating intervals";
    -- print ourRoots;
    -- if ourRoots == {} then error "List has no roots";

    if length(ourRoots)==0 then (
        L1 := {};
      )
      else (
    -- if two consecutive intervals have a shared start/end point that is a root then refine intervals:
      for i from 0 to #ourRoots-2 do (
      -- print("Roots", ourRoots);
        while (ourRoots_i_1)==(ourRoots_(i+1)_0) do (
          intervalSize = intervalSize/2;
          ourRoots = realRootIsolation(h,intervalSize);
        );
      );
    -- Find the mid-points between intervals as cell witnesses:
    L1 = for i from 1 to #ourRoots-1 list (ourRoots_(i-1)_1+ourRoots_i_0)/2;
    -- print "Mid Points:"; print L1;
    -- Add the beginning of the first interval and the end of the last interval to the list, but each of which -+1 in order to avoid them being a root:
    L1 = {(min (flatten ourRoots))-1}|L1|{(max (flatten ourRoots))+1};
    );
    L1
  )

-- Given the list of lists of polynomials that the projection returns creates a CAD in a tree-like hash structure
-- starting from the point p given. i is the level and could be deduced from p but it is sent to ease understanding
liftingPoint = method()
liftingPoint(List, MutableHashTable, List) := (S, p, ordering) -> (
    -- List is a list of lists of polynomials, the first list of polys with i+1 variables (up to n variables, where n is the number of variables in the initial polynomials)
    -- HashTable is a point in i variables
    -- List is the variable ordering followed in the projection
    cell := new MutableHashTable;
    cell#"point" = p;
    i := #keys(p);
    -- we check if all the variables have been given a value already
    if i >= length(S) then return cell; -- if so just return an empty MutableHashTable
    L := evalPolys(S_i, p); -- S is the list of lists of polynomials
    cell#"polynomials"=L;
    print L;
    print S_i;
    print p;
    
    
    -- I want this to ensure that values are returned as values, but including it also breaks tests #12,14,15,16,17.
    --if liftable(L,QQ) then L = lift(p,QQ); -- if a value, return as a value.
    
    -- This function evaluates the point p into the polynomials of S_i
    
    if #support(L) > 1 then error ("Expected list of polynomials to have a single variable as support. The value of L is " | toString(L));
    -- v := (support(L))_0;
    v := ordering_i;
    newSamplePoints := samplePoints(L);
    SNew := drop(S,1);
    for samplePoint in newSamplePoints do (
        pNew := copy p;
        pNew#v = samplePoint;
        cell#samplePoint = liftingPoint(S, pNew, ordering);
        );
    cell
    )

-- Does the open CAD
openCAD = method()
openCAD(List) := (L) -> (
  (S, ordering) := projectionPhase(L);
  p := new MutableHashTable;
  liftingPoint(S, p, ordering)
)

-- Checks if an object contains all the information the other has
-- I've created it for my purpose, but if it is useful it should be possible to generalise
latterContainsFormer = method()
latterContainsFormer(Thing, Thing) := (former, latter) -> (
  if not instance(former, class(latter)) then (
    print("The Things sent are not of the same class.");
    return false
  ); -- maybe I want to use ancestor here
  if instance(former, MutableHashTable) then (
    for key in keys(former) do (
      if not latter#?key then(
        print("Latter MutableHashTable doesnt have that key.");
        return false
      );
      boolean := latterContainsFormer(former#key, latter#key);
      if not boolean then(
        print("The objects stored in former and latter under key are not the same");
        return false
      )
    )
  )
  else if instance(former, List) then (
    -- gives an error if both are lists containing different types of elements, i.e. list of polys vs list of lists, so below check may also be needed.
    classListFormer := {}; 
    classListLatter := {};
    for elt in former do (
      classListFormer = unique(append(classListFormer,class(elt)))
    );
    classListFormer;
    for elt in latter do (
      classListLatter = unique(append(classListLatter,class(elt)))
    );
    classListLatter;
    -- check latter contains all of former's types
    if not unique(join(classListFormer,classListLatter)) === classListLatter then (
      print ("former contains element(s) of a different type!");
      return false
    )
    --if it does, check each element of that type is in latter
    else for elt in classListLatter do (
      ofTypeInLatter:=select(latter,elt); 
      ofTypeInFormer:=select(former,elt);
      --print ofTypeInLatter;
      --print ofTypeInFormer;
      for elemFormer in ofTypeInFormer do (
	    if not any(ofTypeInLatter, elem->elem==(elemFormer)) then (
	      print (concatenate("elemFormer of type ",toString(elt)," is not in latter"));
	      return false
	    )
	  )
    )
  )
  else if former!=latter then (
    print("former and latter are not the same");
    return false
  );
  return true
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
    Evaluates the given polynomial with respect to the given sample point.
  Usage
    evalPolys(p,alpha)
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
	  evalPolys(p,alpha)
          
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  alpha#x3 = -2
	  p=x1^2*x0-2*x3*x2
	  evalPolys(p,alpha)

  SeeAlso
///

--Currently has issues - can't have duplicates and can't seem to combine them into one. How do we fix this?

--doc ///
--  Key
--    (evalPolys, List, MutableHashTable)
--    evalPolys
--  Headline
--    Given a list of polynomials (S) and a sample point (alpha), returns the polynomials of S evaluated at alpha.
--  Usage
--    evalPolys(S,alpha)
--  Inputs
--    S:List
--      list of polynomials as RingElements
--    alpha:MutableHashTable
--      point described using a hash table where the keys are RingElements (variables)
--  Outputs
--    :List
--      List of RingElements describing the polynomials in S evaluated at the sample point.
--  Description
--    Text
--      Given the list of polynomial (S) and sample point (alpha) it evaluates the list polynomial at the sample point and returns that polynomial, by calling evalPolys on each polynomial in S. 	  This is used in the lifting phase of the CAD, where the polynomials in set of polynomials in $k$ variables are evaluated at a point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return univariate polynomials in $\mathbb{R}[x_k]$.
--    Example
--	  R=QQ[x0,x1,x2,x3]
--	  alpha = new MutableHashTable
--	  alpha#x0 = 3
--	  alpha#x1 = 4
--	  alpha#x2 = 1
--	  S = {x1^2*x0-2*x3*x2,x1^3*x0*x2+x3}
--	  evalPolys(S,alpha)
--   SeeAlso
--    evalPolys
--///

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
      of lists of polynomials
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
      pts#x1 = 1
      pts#x2 = 3
      peek pts
      ordering = {x1,x2,x3}
      liftingPoint(L,pts,ordering)
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
    (latterContainsFormer, Thing, Thing)
    latterContainsFormer
  Headline
    Checks if an object contains all the information the other has
  Usage
    latterContainsFormer(former, latter)
  Inputs
    former:Thing
      a thing
    latter:Thing
      a thing	
  Outputs
    :Boolean
      true or false
  Description
    Text
      This function first checks two objects are of the same class, then if they are of type MutableHashTable, it checks they both contain the keys from former and that these keys contain the same objects. If they are lists, it checks they contain the elements from former, and for any other type it checks if they are the the same, returning false if it fails any of these and true otherwise.
    Example
      R=QQ[x1,x2,x3]
      f0=x1*x2
      f1=x1^2*x2-x1*x3+x3^3
      f2=x2^2*x3+x3
      L1={f0,f1}
      L2={f1,f2} 
      P1 = projectionPhase(L1)
      P2 = projectionPhase(L2)
      latterContainsFormer(P1, P2)
  SeeAlso
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
  assert(gmodsHeuristic(L) == x1)
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
  answer = {{x2^2+1,x2}, {x3,x2^2+1,x2,4*x2*x3-1}, {x1*x2,x1^2*x2+x3^3-x1*x3,x2^2*x3+x3}}
  assert(sort P === sort answer)
///

TEST /// -* samplePoints test *-
-- Test 8
  R=QQ[x]
  f=x^2-1
  g=x^3-1
  L1={f,g}
  S = samplePoints(L1)
  answer = {-3, -1/2, 2}
  assert(S == answer)
///

TEST /// -* liftingPoint test *-
-- Test 9
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1*x2+x3^2
  L={p0,p1}
  P = projectionPhase(L)
  pts = new MutableHashTable
  pts#x1 = -1
  pts#x2 = 3
  LP = liftingPoint(P,pts)

  pLevelThreeA = new MutableHashTable from {x3=>3, x1=>-1, x2=>3}
  pLevelThreeB = new MutableHashTable from {x3=>-3, x1=>-1, x2=>3}  
  pLevelTwo = new MutableHashTable from {x1=>-1, x2=>3}
  
  cellLevelThreeA = new MutableHashTable from {"point"=>pLevelThreeA}
  cellLevelThreeB = new MutableHashTable from {"point"=>pLevelThreeB}

  cellLevelTwo = new MutableHashTable from {3_QQ=>cellLevelThreeA, -3_QQ=>cellLevelThreeB, "point"=>pLevelTwo, "polynomials"=>{-3_QQ,x3^2-3}}



  --this all needs rewriting, should just compare hashified.
  
  printWidth=200
  hashify(cellLevelTwo), hashify LP
  keys (hashify cellLevelTwo)
  hashify cellLevelTwo#(3_QQ)#"point"#x1
  hashify LP#(3_QQ)#"point"#x1
  
  
  assert(hashify(cellLevelTwo == hashify LP))


  assert(LP#"polynomials" == cellLevelTwo#"polynomials")
  assert(latterContainsFormer(cellLevelTwo#"point", LP#"point"))
  assert(latterContainsFormer(LP#"point", cellLevelTwo#"point"))
  
  --assert(latterContainsFormer(cellLevelTwo#(-3_QQ), LP#(-3_QQ)))
  --assert(latterContainsFormer(LP#(-3_QQ), cellLevelTwo#(-3_QQ)))
  -- not of same class, objects not the same.
  assert(latterContainsFormer(peek cellLevelTwo#(-3_QQ), peek LP#(-3_QQ)))
  assert(latterContainsFormer(peek LP#(-3_QQ), peek cellLevelTwo#(-3_QQ)))
  --these work.
  
  peek cellLevelTwo#(-3_QQ)
  peek LP#(-3_QQ)
  pairs cellLevelTwo#(-3_QQ)
  pairs LP#(-3_QQ)
  peek pairs cellLevelTwo#(-3_QQ)
  peek pairs LP#(-3_QQ)
  peek values cellLevelTwo#(-3_QQ)
  peek values LP#(-3_QQ)
  --what isn't the same about these?
  
  assert(peek cellLevelTwo#(-3_QQ)==peek LP#(-3_QQ))
  --true in emacs, error in Web
  assert(peek values cellLevelTwo#(-3_QQ)==peek values LP#(-3_QQ))
  --true in emacs, error in Web
  latterContainsFormer(peek values cellLevelTwo#(-3_QQ),peek values LP#(-3_QQ))
  --true in emacs, error in Web
  assert(latterContainsFormer(peek values cellLevelTwo#(-3_QQ),peek values LP#(-3_QQ)))
  --true in emacs, error in Web.
  

  assert(peek values cellLevelTwo#(3_QQ)==peek values LP#(3_QQ))
  
  --assert(latterContainsFormer(cellLevelTwo#(3_QQ), LP#(3_QQ)))
  --assert(latterContainsFormer(LP#(3_QQ), cellLevelTwo#(3_QQ)))
  -- not of same class, objects not the same
  assert(latterContainsFormer(peek cellLevelTwo#(3_QQ), peek LP#(3_QQ)))
  assert(latterContainsFormer(peek LP#(3_QQ), peek cellLevelTwo#(3_QQ)))
  --these work.
  peek cellLevelTwo#(3_QQ)
  peek LP#(3_QQ)

  keys cellLevelTwo
  keys LP

  (keys cellLevelTwo)#1
  (keys LP)#1



  --assert(cellLevelTwo == LP)
  --no method
  assert(latterContainsFormer(peek cellLevelTwo, peek LP))
  assert(latterContainsFormer(peek LP, peek cellLevelTwo))

  --all of these checks are messy and don't work. What is a sufficient check that LP and the constructed thing "are the same"?

  -- for key in keys(LP) do assert(cellLevelTwo#?key)
  -- keys(cellLevelTwo)
  -- keys(LP)
  -- values H
  -- values LP
  -- assert(sort(keys(H)) == sort(keys(LP)))
  -- assert(values(H) == values(LP))
  -- assert(keys(LP#"point") == keys(H#"point")) 
  -- assert(values(LP#"point") == values(H#"point"))
  -- assert(LP#"point" == LP#"point")
  -- assert(LP#"polynomials" == H#"polynomials") 
  -- peek H
  -- peek LP
  -- peek H#"point"
  -- peek LP#"point"
  -- assert(LP == H)
///

TEST /// -* openCAD test smaller *-
-- Test 10
  R=QQ[x1,x2]
  p0=x1^2+x2
  p1=x1^3*x2^2
  L={p0,p1}
  C=openCAD(L)

  pLevelFourA = new MutableHashTable from {x1=>-3/4, x2=>-2_QQ}
  pLevelFourB = new MutableHashTable from {x1=>-5/2, x2=>-2_QQ} 
  pLevelFourC = new MutableHashTable from {x1=>9/16, x2=>-2_QQ} 
  pLevelFourD = new MutableHashTable from {x1=>5/2, x2=>-2_QQ}
  pLevelFourE = new MutableHashTable from {x1=>-2_QQ, x2=>1_QQ}
  pLevelFourF = new MutableHashTable from {x1=>1_QQ, x2=>1_QQ}
  
  cellLevelThreeA = new MutableHashTable from {"point"=>pLevelFourA}
  cellLevelThreeB = new MutableHashTable from {"point"=>pLevelFourB}
  cellLevelThreeC = new MutableHashTable from {"point"=>pLevelFourC}
  cellLevelThreeD = new MutableHashTable from {"point"=>pLevelFourD}
  cellLevelThreeE = new MutableHashTable from {"point"=>pLevelFourE}
  cellLevelThreeF = new MutableHashTable from {"point"=>pLevelFourF}

  pLevelThreeA = new MutableHashTable from {x2=>-2_QQ}
  pLevelThreeB = new MutableHashTable from {x2=>1_QQ}
  
  pLevelTwoA = new MutableHashTable from {-3/4=>cellLevelThreeA, -5/2=>cellLevelThreeB, 9/16=>cellLevelThreeC, 5/2=>cellLevelThreeD, "point"=>pLevelThreeA, "polynomials"=>{x1^2-2,4*x1^3}}
  pLevelTwoB = new MutableHashTable from {-2_QQ=>cellLevelThreeE, 1_QQ=>cellLevelThreeF, "point"=>pLevelThreeB, "polynomials"=>{x1^2+1,x1^3}}  
  pLevelTwoC = new MutableHashTable
  
  cellLevelOne = new MutableHashTable from {-2_QQ=>pLevelTwoA, 1_QQ=>pLevelTwoB, "point"=>pLevelTwoC, "polynomials"=>{x2}}
  hashify pLevelFourA
  peek pLevelFourA
  
  hashify pLevelTwoA
  hashify C
  hashify cellLevelOne, hashify C
  assert(hashify cellLevelOne === hashify C)
  printWidth = 200
  
 keys((hashify C)#(-2_QQ)#(-3/4_QQ)#"point")
 oo/ring  
  
 keys((hashify cellLevelOne)#(-2_QQ)#(-3/4_QQ)#"point")
 oo/ring  
  
  peek cellLevelOne
  peek C

  assert(peek cellLevelOne == peek C)
  assert(latterContainsFormer(peek cellLevelOne, peek C))
  assert(latterContainsFormer(peek C, peek cellLevelOne))
///

TEST /// -* latterContainsFormer test *-
-- Test 11
  R=QQ[x1,x2,x3]
  f0=x1*x2
  f1=x1^2*x2-x1*x3+x3^3
  f2=x2^2*x3+x3
  L1={f0,f1}
  L2={f1,f2} 
  P1 = projectionPhase(L1)
  P2 = projectionPhase(L2)
  lcf1 = latterContainsFormer(P1, P2)
  lcf2 = latterContainsFormer(P1, P1)  
  lcf3 = latterContainsFormer(L1, P1)  
  assert(lcf1 == false)
  assert(lcf2 == true)
  assert(lcf3 == false)
///

TEST /// -* positivePoint test 1*-
-- Test 12
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
-- Test 13
  R=QQ[x]
  p0=x^2-1
  p1=x
  L={p0,p1}
  C=openCAD(L)
  PP=positivePoint(L,C)
  answer = new MutableHashTable from {
      x => 2}
  assert(peek PP == peek answer)
  assert(latterContainsFormer(peek PP,peek answer))
  assert(latterContainsFormer(peek answer,peek PP))
  --these work in emacs. Is this enough?
  
  peek PP
  peek answer
  peek pairs PP
  peek pairs answer
  
  assert((peek pairs answer) == (peek pairs PP))
  assert(latterContainsFormer(peek pairs answer, peek pairs PP))
  --these are fine in emacs. Is this enough? It still seems to give an error for test 13
///

TEST /// -* findSolution test 1*-
-- Test 14
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  L={p0,p1,p2}
  assert(findSolution(L) == true)
///

TEST /// -* findSolution test 2*-
-- Test 15
  R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1^2*x2-x1*x3+x3^3
  p2=x2^2*x3+x3
  p3=-x1*x2
  L={p0,p1,p2,p3}
  assert(findSolution(L) == false)
///

TEST /// -* findSolution test 3*-
-- Test 16
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
-- Test 17 
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
debug needsPackage "CADecomposition"
needsPackage "CADecomposition"
check "CADecomposition"

restart
uninstallPackage "CADecomposition"
restart
installPackage "CADecomposition"
viewHelp "CADecomposition"
installPackage("CADecomposition",IgnoreExampleErrors=>true)

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
