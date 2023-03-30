///
	Root Isolation for Several Polynomials:
	Input:
		L: List of polynomials,
		r: integer, rational or real number
///

samplePoints = method()
loadPackage "RealRoots";
for A in {ZZ,QQ,RR} do
samplePoints(List,A) := (L,r) -> (
    h=product L;
    -- print h;
    L  := realRootIsolation(h,r);
    print("root isolating intervals", L);
    L1:=for i from 1 to #L-1 list (L_(i-1)_1+L_i_0)/2;
    L2:=append(prepend(L_0_0,L1),L_(#L-1)_1)
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