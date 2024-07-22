--ORDER FOR WEB

restart
check "CADecomposition" --run tests
uninstallPackage "RealRoots"
installPackage "RealRootsNew" --while we wait for RealRoots to update, this is the fixed version
installPackage("CADecomposition")

--======================




installPackage("CADecomposition")


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

--EXAMPLE TO RUN THROUGH FOR PAPER--
--Jirstrand example

R=QQ[x1,x2]
p1:=x1^2+x2^2-1
p2:=x1^3-x2^2
L={p1,p2}

findSolution(L)
hashify openCAD(L)

--now do all the related commands: 

--projectionPhase if that makes sense, gmodsHeuristic at each bit, lazardProjection at each bit, 
--liftingPoint, evalPolys, samplePoints (realRootIso)
--leadCoeff,factorsInList,factors








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

L1 := for p in L list leadCoeff(p,GML) --leading coefficients
L2 := for p in L list p-GML*contract(GML,p) --trailing coefficients
L3 := for p in L list discriminant(p,GML) --discriminants
L4 := for p in subsets(L,2) list resultant(p_0,p_1,GML) --resultants


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
timing C2 = openCAD(L)
-- 4.8998 seconds

R = QQ[x1,x2,x3,x4]
L = {(x1-1)^2+(x2-1)^2+(x3-1)^2+(x4-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2+(x4+1)^2-2^2}
timing C4 = openCAD(L)
-- 1503.43 seconds

--This probably takes a day!

--R = QQ[x1,x2,x3,x4,x5]
--L = {(x1-1)^2+(x2-1)^2+(x3-1)^2+(x4-1)^2+(x5-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2+(x4+1)^2+(x5+1)^2-2^2}
--timing C5 = openCAD(L)








var = gmodsHeuristic(L,support(L))
lazardProjection(L,var)
(S,ordering) = projectionPhase(L)

samplePoints(S#0) --this is one of the crazy parts

--==========================
j:=3;
R :=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9,x10]
VAR:=x1*x2*x3*x4*x5*x6*x7*x8*x9*x10
varlist:=support(VAR);
--R := QQ[varlist];
--vlist:=varlist;
L = {};
for i from 1 to j do (
--R1 = QQ[take(varlist, i)];
S={sum (apply(take(varlist,i) ,k->(k-1)^2)) - 4, sum (apply(take(varlist,i) ,k->(k+1)^2)) - 4};
L = append(L,S);
)
L

for i from 1 to j do (
L1 := L_(#L-i);
R1 := QQ[support(L1)];
L2 := {sub(L1_0,R1),sub(L1_1,R1)};
print concatenate(toString(#L-i+1)," variables:"); print elapsedTiming openCAD(L2);
)

--make it so it adds all of these to a list maybe so I can check them again sometime

--the 4d one took ~30 mins on a good day. Try it again soon and work through it:

CAD = openCAD(L_3);
peek CAD
CAD#"polynomials"
CAD#((keys CAD)_0)
peek oo

--and repeat this to get one branch

--=========================
R=QQ[x]
positivePoint({3-x^2,(7*x-12)*(x^2+x+1)})


--===================================
R=QQ[x]
findPositiveSolution({3-x^2,(7*x-12)*(x^2+x+1)})
