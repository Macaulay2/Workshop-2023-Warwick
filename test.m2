needsPackage "SubalgebraBases"
needsPackage "InvariantRing"

R = QQ[x,y,z]
S = subring {x*y*z, x*y + x*z + y*z, x + y + z}
gens sagbi S

SB = sagbi S
peek SB

------------
x = 10
f = n -> (
    -- inside the function
    x := symbol x;
    y := symbol y;
    R := QQ[x_1 .. x_n, y_1 .. y_n];
    if true then (
	s := 1
	);
    s
    )
f(10)
vars oo
x
