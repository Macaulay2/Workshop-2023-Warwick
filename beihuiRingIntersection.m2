path = prepend("./", path)
needsPackage "SubalgebraBases"

R = QQ[x_1, y_1, x_2, y_2]

f = x_2^2*y_2 + y_2^3
g = y_2^2+x_2*y_2 - y_2 

intersectSubs = (f, g) -> (
    assert(ring f === R);
    assert(ring g === R);
    
    I := ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g);
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
adksfjhakdj



-- we should write substitute for subrings
