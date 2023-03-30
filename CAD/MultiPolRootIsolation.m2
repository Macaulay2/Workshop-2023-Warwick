///
	Root Isolation for Several Polynomials:
	Input:
		L: List of polynomials,
		r: integer, rational or real number
///

MultiRootIsolation = method()
loadPackage "RealRoots";
for A in {ZZ,QQ,RR} do
MultiRootIsolation(List,A) := (L,r) -> (
    h=product L;
    -- print h;
    realRootIsolation(h,r)
    )

-- Tests
R=QQ[x]
f=x^2-1
g=x^3-1
L1={f,g}
MultiRootIsolation(L1,1/2)

f1=5*x^3+1
g1=x^2-1
h1=1/2*x^5+3*x-1
L2={f1,g1,h1}
MultiRootIsolation(L2,3)

