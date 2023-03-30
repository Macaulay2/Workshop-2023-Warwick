evalPoly = method()

evalPoly(RingElement,MutableHashTable) := (p, alpha) -> (
        for k in keys(alpha) do
          p=sub(p, {k => alpha#k});
	p
      )

evalPolyList = method()

evalPolyList(List,MutableHashTable) := (S, alpha) -> (
  S1 = for p in S list
    evalPoly(p,alpha);
  S1
)

--Example
R=QQ[x0,x1,x2,x3]
points = new MutableHashTable
points#x0 = 3
points#x1 = 4
points#x2 = 1
S_0 = {x1^2*x0-2*x3*x2,x1^3*x0*x2+x3}
evalPolyList(S_0,points)
