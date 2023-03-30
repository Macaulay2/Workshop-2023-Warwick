-- Examples of adjunction.

restart
needsPackage "SurfacesInP4"
surfacesInP4(Degree => 8)
I = example "k3.d8.g6"
betti res I
surfaceInvariants I
K = canonicalModule I
K = prune K
basis(1, K)
R = S/I
K = K ** R

basis(1, K)
prune oo
basis(1, oo)

H = Hom(K, R)
basis H
degrees H
peek basis (2,H)
viewHelp random 
homomorphism (basis (2,H))_{0}
source basis (2,H)

M = basis (2,H)
source M
random (source M, R^{-2})
phi = homomorphism H_{0}
source phi
target phi
degree phi
ker phi == 0
J = ideal (image phi)
betti J

-- Method to return canonical ideal 
I = example "k3.d8.g6"
(d, J) = canonicalIdeal(I)
assert(numcols basis(d+1,J) == 7)

--

Hom(K, R)
super basis(2, Hom(K, R))
oo * random(R^10, R^1)
KR = ideal oo
betti KR
super basis(3, KR)
P6 = (coefficientRing ring I)[a,b,c,d,e,f,g]
imI = trim kernel map(ring J, P6, super basis(3, J))
betti imI

J = kernel map(ring KR, P6, super basis(3, KR))
dim J
betti res J

X' = variety J
HH^0(OO_X')
HH^1(OO_X')
HH^2(OO_X')
degree J

