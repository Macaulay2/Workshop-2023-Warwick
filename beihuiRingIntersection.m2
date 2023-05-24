path = prepend("./", path)
needsPackage "SubalgebraBases"

--R = QQ[x_1, y_1, x_2, y_2, MonomialOrder => Lex]
R = QQ[x_1, y_1, x_2, y_2]


intersectSubs = (f, g) -> (
    assert(ring f === R);
    assert(ring g === R);
    
    I := ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g);
    --J := ideal(x_1*x_2, x_1*y_2, y_1*x_2, y_1*y_2);
    --Q := R/(I+J);
    Q := R/I;
    m := map(Q, R, vars Q);
    S1 := subring {m(x_1), m(y_1)};
    S2 := subring {m(x_2), m(y_2)};
    
    S12 := subringIntersection(S1, S2);
    
    -- we could check if it is full intersection:
    assert(isFullIntersection S12);
    
    gens S12
    )

end --

restart
load "beihuiRingIntersection.m2"
f = -y_2
g = x_2 - y_2*(x_2-1)^2
intersectSubs(f, g)
gens sagbi oo

I = ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g);
transpose leadTerm I

-- compute a basis for degree up to 6
-- the sagbi basis is monomial so we can just take these
L = monomials (y_2 + x_2 + y_1 + 1)^6
M = L % (leadTerm I)
compress oo
transpose oo -- k-vectorspace basis for G_d


-- count the number of monomials 
use R

for i from 1 to 15 do (
    L := monomials (y_2 + x_2 + y_1 + 1)^i;
    M := L % (leadTerm I);
    print(i, numcols compress M);
    )

-- initial subring 
-- S subring of R/I
-- in(S) subring of R/in(I)

-- we should write substitute for subrings
-- we should write a leadTerm Subring function

needsPackage "AlgebraicSplines"

-- R+R --> R/I

load "beihuiRingIntersection.m2"
f = -y_2
g = x_2 - y_2*(x_2-1)^2
--intersectSubs(f, g)
--gens sagbi oo

I = ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g);

L = R^2
C = comodule I

phi = map(C, L, {{1, -1}})
k = ker phi


R' = QQ[x_1, y_1, x_2, y_2, e_1, e_2]
Q = R'/ideal(e_1^2 - e_1, e_2^2 - e_2, e_1*e_2, e_1+e_2-1)

mapGens = sub(gens k, Q)
subringGens = matrix {{e_1, e_2}} * mapGens 

S = subring subringGens -- generators of phi as an algebra
T = subring {x_1*e_1, y_1*e_1, x_2*e_2, y_2*e_2} -- algebra representing the elimination

ST = subringIntersection(S, T, PrintLevel => 1, Limit => 6)
ST = subringIntersection1(S, T, PrintLevel => 1)
ST = subringIntersection1(T, S, PrintLevel => 1, Limit => 10)


