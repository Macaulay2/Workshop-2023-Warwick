-- Here are some of the "special cases" in the adjunction theorem for surfaces

-- theorem 1.10 in DES.

-- example (5).
-- 7 points in P4, want sextics double through the 7 points.
  restart
  needsPackage "SurfacesInP4"
  needsPackage "Points"
  kk = ZZ/32003
  P2 = kk[x_0..x_2]
  P4 = kk[t_0..t_4]
  M = randomPointsMat(P2, 7)
  Mkk = lift(M, kk)
  (inI, I) = projectiveFatPoints(Mkk, {2,2,2,2,2,2,2}, P2)
  I = trim ideal I

  elems = super basis(6, I) * random(P2^7, P2^5)
  phi = map(P2, P4, elems)
  J = trim ker phi
  betti res J
  degree J
  codim J
  decompose(J + minors(codim J, jacobian J)) -- upshot: generic projection to P4 is not smooth!

P6 = kk[y_0..y_6]
phi2 = map(P2, P6, super basis(6, I))
J2 = trim ker phi2
betti res J2

degree J2
sectionalGenus J2
singJ2 = saturate trim(J2 + minors(codim J2, jacobian J2)) -- smooth
KX = prune canonicalModule J2
H = (P6^1/J2) ** P6^{1}
intersectionMatrix(J2, {H, KX})
intersectionProduct(J2, H ** KX, H ** KX)
HH^0(sheaf(H ** KX))

