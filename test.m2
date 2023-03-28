needsPackage "SubalgebraBases"
needsPackage "InvariantRing"

R = QQ[x,y,z]
S = subring {x*y*z, x*y + x*z + y*z, x + y + z}
gens sagbi S
