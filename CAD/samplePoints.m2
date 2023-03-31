-- Given a list of univariate polynomials, samplePoints prduces sample points for the cells (seperating the roots)
samplePoints = method()
samplePoints(List) := (L) -> (
    A := QQ(monoid[support(L)]);
    h:=sub(product L, A);
    print("L"); print L;
    print h;
    ourRoots := realRootIsolation(h,1); -- when RealRoots is evaluating h they get an element of R, not a number
    print("root isolating intervals", ourRoots);
    -- if two consecutive intervals have a shared start/end point tha tis a root then refine intervals:
    for i from 0 to #ourRoots-1 do
      if ourRoot_i_1=ourRoot_(i+1)_0 then ourRoots = realRootIsolation(h,1/2);
    -- Find the mid-points between intervals as cell witnesses:
    L1:=for i from 1 to #ourRoots-1 list (ourRoots_(i-1)_1+ourRoots_i_0)/2;
    -- Add the beginning of the first interval and the end of the last interval to the list, but each of which -+1 in order to avoind them being a root:
    L2:=append(prepend(ourRoots_0_0-1,L1),ourRoots_(#ourRoots-1)_1+1)
    )

-- Tests
R=QQ[x]
f=x^2-1
g=x^3-1
L1={f,g}
samplePoints(L1,1/2)

f1=5*x^3+1
g1=x^2-1
h1=1/2*x^5+3*x-1
L2={f1,g1,h1}
S:=samplePoints(L2,3)