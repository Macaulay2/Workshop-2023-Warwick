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
f1:=x1^2+x2^2-1
f2:=x1^3-x2^2
F={f1,f2}

findPositiveSolution(F)
hashify openCAD(F)
positivePoint(F,openCAD(F))
peek positivePoint(F,openCAD(F))

openCAD(F)
peek(openCAD(F))

  R=QQ[x1,x2,x3]
  ff0=x1*x2, ff1=x1^2*x2-x1*x3+x3^3, ff2=x2^2*x3+x3;
  F1={pp0,pp1,pp2}
  CAD = new HashTable from {x2=>1_QQ, x3=>5/4, x1=>1_QQ};
  CAD2 = new HashTable from {x2=>1_QQ, x3=>5/4};
  assert(findPositiveSolution F1 === (true, CAD))
  assert(findPositiveSolution F1 === (true, CAD2))
  positivePoint(F1,CAD)
  
positivePoint(F1,openCAD(F1))

--now do all the related commands: 

--projectionPhase if that makes sense, gmodsHeuristic at each bit, lazardProjection at each bit, 
--liftingPoint, evalPolys, samplePoints (realRootIso)
--leadCoeff,factorsInList,factors


lazardProjection(F,x2)
samplePoints(lazardProjection(F,x2))

alpha1 = new MutableHashTable; alpha1#x1 = -5/2;
evalPolys(F,alpha1)
samplePoints(evalPolys(F,alpha1))

alpha2 = new MutableHashTable; alpha2#x1 = -3/4
evalPolys(F,alpha2)
samplePoints(evalPolys(F,alpha2))


(PP,ord) = projectionPhase(F);

LP1 = liftingPoint(PP,ord,alpha1)
peek LP1
hashify LP1

LP2 = liftingPoint(PP,ord,alpha2)
peek LP2
hashify LP2

openCAD(F)
hashify openCAD(F)
alpha = new MutableHashTable -- this is a test, this a solution!
alpha#x1 = 2
alpha#x2 = 1
evalPolys(F,alpha)

factors(p1)
factors(p2)
support(F)
factorsInList(F)

GMF:=gmodsHeuristic(F,support(F))

leadCoeff(p1,GMF)
leadCoeff p2,GMF)

F1 := for p in F list leadCoeff(p,GMF) --leading coefficients
F2 := for p in F list p-GMF*contract(GMF,p) --trailing coefficients
F3 := for p in F list discriminant(p,GMF) --discriminants
F4 := for p in subsets(F,2) list resultant(p_0,p_1,GMF) --resultants


lazardProjection(F,GMF)

projectionPhase(F);

samplePoints(lazardProjection(F,GMF));

--==========================================================

 R=QQ[x]
  f=x^2-1
  g=x^3-1
  F1={f,g}
  S = samplePoints(F1)

--x^4+x^3-x-1

--============================

R=QQ[x1,x2,x3]
  p0=x1*x2
  p1=x1*x2+x3^2
  F={p0,p1}
  (P,ord) = projectionPhase(F)
  pts = new MutableHashTable
  pts#x1 = -1
  pts#x2 = 3
  --ord = {x2,x1,x3}
  LP = liftingPoint(P,ord,pts)

--========================

--big example: intersecting sphere. This is 3-dim and takes about 58 seconds.
R = QQ[x1,x2,x3]
F = {(x1-1)^2+(x2-1)^2+(x3-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2-2^2}
timing C2 = openCAD(F)
-- 4.8998 seconds

R = QQ[x1,x2,x3,x4]
F = {(x1-1)^2+(x2-1)^2+(x3-1)^2+(x4-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2+(x4+1)^2-2^2}
timing C4 = openCAD(F)
-- 1503.43 seconds

--This probably takes a day!

--R = QQ[x1,x2,x3,x4,x5]
--F = {(x1-1)^2+(x2-1)^2+(x3-1)^2+(x4-1)^2+(x5-1)^2-2^2,(x1+1)^2+(x2+1)^2+(x3+1)^2+(x4+1)^2+(x5+1)^2-2^2}
--timing C5 = openCAD(F)








var = gmodsHeuristic(F,support(F))
lazardProjection(F,var)
(S,ordering) = projectionPhase(F)

samplePoints(S#0) --this is one of the crazy parts

--==========================
j:=3;
R :=QQ[x1,x2,x3,x4,x5,x6,x7,x8,x9,x10]
VAR:=x1*x2*x3*x4*x5*x6*x7*x8*x9*x10
varlist:=support(VAR);
--R := QQ[varlist];
--vlist:=varlist;
F = {};
for i from 1 to j do (
--R1 = QQ[take(varlist, i)];
S={sum (apply(take(varlist,i) ,k->(k-1)^2)) - 4, sum (apply(take(varlist,i) ,k->(k+1)^2)) - 4};
F = append(F,S);
)
F

for i from 1 to j do (
F1 := F_(#F-i);
R1 := QQ[support(F1)];
F2 := {sub(F1_0,R1),sub(F1_1,R1)};
print concatenate(toString(#F-i+1)," variables:"); print elapsedTiming openCAD(F2);
)

--make it so it adds all of these to a list maybe so I can check them again sometime

--the 4d one took ~30 mins on a good day. Try it again soon and work through it:

CAD = openCAD(F_3);
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



R=QQ[x]
L = {(x-1/2)*(x+1/2)*x}
samplePoints(L)

A := QQ(monoid[support(L)]);
    h:=sub(product L, A);
    intervalSize := 1; 
    ourRoots := realRootIsolation(h,intervalSize)


ourRoots := realRootIsolation(h,intervalSize/2)
ourRoots := realRootIsolation(h,intervalSize/4)

#ourRoots

SP = for i from 0 to #ourRoots-2 list (ourRoots_i_1+ourRoots_(i+1)_0)/2
{((min (flatten ourRoots))-1)_QQ}|SP|{((max (flatten ourRoots))+1)_QQ}
