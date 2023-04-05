-- experiments with the kernel of the ring maps
restart
needsPackage "SubalgebraBases"
debug SubalgebraBases

ambTTilde = QQ[x_1, y_1, x_2, y_2, e_1, e_2, Degrees => {1,1,1,1,0,0}]
use ambTTilde
-- Ttilde = subring {x_1*e_1, y_1*e_1, x_2*e_2, y_2*e_2, e_1, e_2}

R = QQ[x_1, y_1, x_2, y_2]
f = -y_2
g = x_2 - y_2*(x_2-1)^2
I = ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g)
Q = R/I

phiTildeAmb = map(Q, ambTTilde, {x_1, y_1, x_2, y_2, 1_R, 1_R})
ker phiTildeAmb

-- peek Ttilde
-- presRing = Ttilde#"subductionQuotientRing"
presRing = QQ[p_0 .. p_5, Degrees => {1,1,1,1,0,0}]
use ambTTilde
presentationMap = map(ambTTilde, presRing, {x_1*e_1, y_1*e_1, x_2*e_2, y_2*e_2, e_1, e_2}) 
presIdeal = ker presentationMap
vars presRing

-- ker phiTilde inside Ttilde
-- phiTilde: x_1e_1 (p_0) --> x_1 in Q
-- ker phiTilde  === presentationMap^-1 ker phiTildeAmb
-- Ttilde \cong presRing / ker presentationMap

TtildeQuot = presRing / (ker presentationMap)


use Q
phiTilde = map(Q, TtildeQuot, {x_1, y_1, x_2, y_2, 1_R, 1_R})
kerPhiTilde = ker phiTilde
gens gb I -- compare 

use presRing
vars presRing 
e1 = presRing_4
e2 = presRing_5
-- T = presRing / (ker presentationMap + (e_1^2 - e_1 ... ))
-*
Tideal = (ker presentationMap) + ideal(
    e1^2 - e1, e2^2 - e2, e1*e2, e1+e2-1
    )
T = presRing / Tideal
hilbertFunction(1, coker gens Tideal) -- why doesn't this work??
transpose basis(2, T)
*-

-- QEamb = QQ[(x := symbol x; y := symbol y; e := symbol e; {x_1, y_1, x_2, y_2, e_1, e_2}), Degrees => {1,1,1,1,0,0}]
-- use QEamb
use ambTTilde
TIdeal = ideal(
    e_1^2 - e_1, e_2^2 - e_2, e_1*e_2, e_1+e_2-1
    )


-- QE = QEamb / QEIdeal

-- vars QE
-- vars presRing
m = map(ambTTilde / TIdeal, presRing, {x_1*e_1, y_1*e_1, x_2*e_2, y_2*e_2, e_1, e_2})
ker m 
-- T = QQ[x_1e_1 ...] / (e_1^2-e_1...) \cong presRing / (ker: p_0 --> x_1*e_1 ... \in ambTTilde / TIdeal)

T = presRing / (ker m)
transpose basis(4, T)

TtildeQuot -- presRing / ker presentationMap 
gensKerPhiTilde = gens kerPhiTilde
piMap = map(T, TtildeQuot, vars T)
piMap gensKerPhiTilde

ideal T + kerPhiTilde
