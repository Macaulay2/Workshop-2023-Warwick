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

f = -y_2
g = x_2 - y_2*(x_2-1)^2
intersectSubs(f, g)
gens sagbi oo
leadTerm I
gens I
transpose gens I
transpose gens gb I
transpose leadTerm I

-- we should write substitute for subrings
