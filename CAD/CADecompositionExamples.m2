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
installPackage "RealRootsNew" --while we wait for RealRoots to update, this is the fixed version
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
