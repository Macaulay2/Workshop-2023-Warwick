----------------------------------------------
-- Some tasks for Wednesday at the Workshop --
--
-- Quick note: open M2 in the correct folder
--             by navigating in M-x shell to
--             to the github repo location F12  
--
-- Reminder for Oliver:
-- path = prepend("./", path)
--

needsPackage "SubalgebraBases"
-- peek oo -- want: source directory => .../Workshop-2023-Warwick/

needsPackage "FourTiTwo"

-- Overview -- 
-- Determine how to go from a 1xn matrix of polynomials
-- to a 'matrix of exponents of lead terms'

leadTermExponents = M -> transpose matrix apply( 
                            flatten entries M, 
                            m -> first exponents leadTerm m
                            )

-- small running example
R = QQ[x,y]
M = matrix {{x^2+x*y, x*y + y^2, x^3*y^2 - x^2*y^3}}
M^{0}
flatten exponents 

first exponents (leadTerm first first entries M)

flatten M
leadTermExponents M
viewHelp List

S = QQ[p_1, p_2, p_3]


-- TASK
-- apply the function "exponents" to each "leadTerm" of each entry of the matrix
-- and make the result into a matrix with one column for each exponent
-- then apply toricGroebner to the output
leadTerm M_(0,0)
apply({1,2,3}, x -> x^2)

A = matrix {{2, 1, 3}, {0, 1, 2}}
toricMarkov(A, S) -- a minimal generating set
toricGroebner(A, S) -- a Groebner basis

-- TASK --
-- Work out what term order is being used by toricGroebner?

help toricGroebner
-- come up with examples to figure it out or ask someone that knows


-- TASK (the tricky part)
-- make a new Strategy for subduction called "4ti2"
-- (do this by copying the code for "DegreeByDegree")
-- 
-- 1. do some checks to make sure:
-- a) the ambient ring is not a quotient
zero ideal R
I = ideal(x^2-y)
Q = R/I
zero ideal Q

-- b) make sure the term order is the same as the one that toricGroebner wants
(options R).MonomialOrder

-- 1.1 if any of these checks fail, then fall back on another strategy (or throw an error)

-- 2. copy over DegreeByDegree code to update all the maps and rings
-- 3. modify the part where we set the "SIdeal" is computed
--    using the solutions to the previous tasks
-- 4. Dangerous part! forceGB to make the generators from toricGroebner a GB
--    only ever use forceGB when you know you have a GB

G = matrix {{x^10 + y, x*y + y, y^10 + y^2}}
forceGB G
I = ideal G
gens gb I -- uh oh! that's not a GB
peek G -- the GB is stuck in the cache of the matrix
H = matrix {{x^10 + y, x*y + y, y^10 + y^2}}
J = ideal H
gens gb J

R = QQ[x,y,z] 
-- S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}
benchmark "(S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}; sagbi(S, Strategy=>\"FourTiTwo\"))"
benchmark "(S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}; sagbi(S))"

-*
i18 : benchmark "(S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}; sagbi(S, Strategy=>\"FourTiTwo\"))"

o18 = .0443313953488372

o18 : RR (of precision 53)

i19 : benchmark "(S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}; sagbi(S))"

o19 = .044921875

o19 : RR (of precision 53)
*-

R = QQ[x,y,z] 
S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}
SB = sagbi(S)


-- 5. the reduction ideal is equal to the SIdeal when ambient ring is not a quotient


---------------------------------------------------
-- HARD TASK (We should probably ask Michael Burr)
-- Recall how the 'Incremental Strategy' works
-- Can we implement "Incremental + 4ti2"


---------------------------------------------------
-- Guesses:
-- I suspect that toricGroebner uses GRevLex


-------------------------











path = prepend("./", path)
needsPackage "SubalgebraBases"

R = QQ[x,y,z] 
S = subring {x^2-y, y^3-2*x+z^3, x^3-z^7}
SB = sagbi(S)
gens SB
leadTerm S

sagbi(S, Strategy => "FourTiTwo")
gens oo

needsPackage "MatchingFields" -- one day this will exist in M2 (currently on Ollie's github)
L = diagonalMatchingField(3, 6)
S = subring L
transpose gens oo 
sagbi S
k = 3
n = 6

time (
    L := diagonalMatchingField(k, n);
    S := subring L;
    sagbi(S, Strategy => "FourTiTwo", AutoSubduce => false, PrintLevel => 0)
    )

time ( -- current strategy
    L := diagonalMatchingField(k, n);
    S := subring L;
    sagbi(S, Strategy => "Master", AutoSubduce => false, PrintLevel => 0)
    )

time (
    L := diagonalMatchingField(k, n);
    S := subring L;
    sagbi(S, Strategy => "DegreeByDegree", AutoSubduce => false, PrintLevel => 0)
    )

time (
    L := diagonalMatchingField(k, n);
    S := subring L;
    sagbi(S, Strategy => "Incremental", AutoSubduce => false, PrintLevel => 0)
    )
-------------

time (
    L := diagonalMatchingField(k, n);
    S := subring L;
    isSAGBI(S, Strategy => "FourTiTwo", PrintLevel => 1)
    )

time (
    L := diagonalMatchingField(k, n);
    S := subring L;
    isSAGBI(S, Strategy => "Master", PrintLevel => 1)
    )


