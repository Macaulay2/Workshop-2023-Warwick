-- restart
-- path = prepend("./", path)

needsPackage "SubalgebraBases"
-- peek oo -- want: source directory => .../Workshop-2023-Warwick/

needsPackage "FourTiTwo"

-- Overview -- 
-- Determine how to go from a 1xn matrix of polynomials
-- to a 'matrix of exponents of lead terms'

-- small running example
R = QQ[x,y]
M = matrix {{x^2+x*y, x*y + y^2, x^3*y^2 - x^2*y^3}}
S = QQ[p_1, p_2, p_3]


-- TASK
-- apply the function "exponents" to each "leadTerm" of each entry of the matrix
-- and make the result into a matrix with one column for each exponent

first exponents leadTerm M_(0,0)


A = matrix {{2, 1, 3}, {0, 1, 2}}
toricMarkov(A, S) -- a minimal generating set
toricGroebner(A, S) -- a Groebner basis

-- TASK --
-- Work out what term order is being used by toricGroebner?

help toricGroebner

-- TASK 
-- make a new Strategy for subduction called "4ti2"
-- (do this by copying the code for "DegreeByDegree")
-- 
-- do some checks to make sure:
-- the ambient ring is not a quotient

zero ideal R
I = ideal(x^2-y)
Q = R/I
zero ideal Q

-- make sure the term order is the same as the one that toricGroebner wants
(options R).MonomialOrder


-- HARD TASK (We should probably ask Michael Burr)
-- Recall how the 'Incremental Strategy' works
-- Can we implement "Incremental + 4ti2"
