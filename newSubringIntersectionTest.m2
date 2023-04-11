path = prepend("./", path)
needsPackage "SubalgebraBases"
peek oo
options subringIntersection1
methods subringIntersection1

R = QQ[x,y]
S1 = subring {x^3, y^3}
S2 = subring {x*y^2, x^2*y}

I1 = subringIntersection(S1, S2)
gens I1
isFullIntersection I1

I2 = subringIntersection1(S1, S2)
gens I2
isFullIntersection I2


Q = R/ideal(x^3 + x*y^2 + y^3)
A1 = subring {x^2, x*y}
A2 = subring {x, y^2}

I1 = subringIntersection(A1, A2)
gens I1
gens sagbi I1
isFullIntersection I1

I2 = subringIntersection1(A1, A2)
gens I2
gens sagbi I2
isFullIntersection I2

subduction(I1, gens sagbi I2)
subduction(sagbi I2, gens I1) -- this seems like a bit of a problem!
-- x*y^3 should be a sagbi generator!
-- is the elimination term order working correctly??

peek I2#"compositeSubring"
peek I1#"compositeSubring"

gens I2
gens I1

gens sagbi I2#"compositeSubring"
interGens = selectInSubring(1, gens sagbi I2#"compositeSubring") 
m = map(Q, ring gens sagbi I2#"compositeSubring", matrix {{0_Q, 0_Q}} | gens A2) 
interGens
m interGens -- not a sagbi basis

I3 = subringIntersection1(A2, A1)
gens I3
gens I2
gens sagbi I3

-- it feels like we have two different 'perspectives' for the intersection
-- the union of the generators of I2 and I3 is a sagbi basis for the intersection
-- is this true in general??
