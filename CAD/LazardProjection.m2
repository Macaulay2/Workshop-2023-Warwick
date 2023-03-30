leadCoefficient(RingElement, RingElement) := (p, v) -> (
        d := degree(v,p);	
	contract(v^d,p)
	)
	    
LazardProjection = method()
LazardProjection(List, RingElement) := (L,v) -> (
        L0 := select(L, p -> not member(v,support(p)));
        print L0;
        L = select(L, p -> member(v,support(p)));
        print L;
        L1 := for p in L list leadCoefficient(p,v);		
        print L1;
	L2 := for p in L list discriminant(p,v);	
        print L2;
	L3 := for p in subsets(L,2) list resultant(p_0,p_1,v);			
        print L3;
	L0|L1|L2|L3
	)

---Testing Projection:---
R=QQ[x1,x2,x3]
f0=x1*x2
f1=x1^2*x2-x1*x3+x3^3
f2=x2^2*x3+x3
f3=5*x1
L={f0,f1,f2,f3}

L2 = LazardProjection(L,x1)

leadCoefficient(RingElement, RingElement) := (p, v) -> (
    d := degree(v,p);
    contract(v^d,p)
    )

support(List) := (L) -> (
    unique(flatten(L/support))
    )

fullProjection = method()
fullProjection(List) := (L) -> (
    -- List is list of multivariate polynomials
    S = {L};
    while length(support(L)) > 1 do (
        L = LazardProjection(L, (support(L))_0);
        S = append(S,L);
        );
    S
    )

R = QQ[x,y,z]
p1 = x^2*z^3-y*z
p2 = x^4*z^1*y^2+x^2-1

L = {p1,p2}

fullProjection(L)

p = new MutableHashTable
p#x0

Node = method()
Node(MutableHashTable, Integer, List) := (p,i,S) -> (
    h = new MutableHashTable;
    -- HashTable is a point in i variables 
    -- List is a list of lists of polynomials, the first list of polys with i+1 variables
    L = evalPolyList(S_i, p); -- S is the list of lists of polynomials
    -- This function evaluates the point p into the polynomials of S_i
    v = support(L);
    samplePoints = RootIsolation(L);
    SNew = drop(S,1)
    for samplePoint in samplePoints (
        pNew = p
        pNew#v = samplePoint
        h#samplePoint = Node(pNew,i+1,S)
        )
    )

