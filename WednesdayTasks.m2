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

-- small running example
R = QQ[x,y]
M = matrix {{x^2+x*y, x*y + y^2, x^3*y^2 - x^2*y^3}}
S = QQ[p_1, p_2, p_3]


-- TASK
-- apply the function "exponents" to each "leadTerm" of each entry of the matrix
-- and make the result into a matrix with one column for each exponent
-- then apply toricGroebner to the output
first exponents leadTerm M_(0,0)
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

-- 1.1 if any of these checks fail, then fall back on another strategy

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
-- 5. the reduction ideal is equal to the SIdeal when ambient ring is not a quotient


---------------------------------------------------
-- HARD TASK (We should probably ask Michael Burr)
-- Recall how the 'Incremental Strategy' works
-- Can we implement "Incremental + 4ti2"


---------------------------------------------------
-- Guesses:
-- I suspect that toricGroebner uses GRevLex
