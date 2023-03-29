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
	-- L0|L1|L2|L3
        L = apply(L0|L1|L2|L3, p -> toList(factor(p)));
        print L;
        L = unique(flatten(L));
        print L;
        L = apply(L, p -> radical(ideal(p))); 
        -- Error: factors are Expressions of class Power: 
        -- ideal cannot be applied to those
        print L	)

---Testing Projection:---
R=QQ[x1,x2,x3]
f0=x1*x2
f1=x1^2*x2-x1*x3+x3^3
f2=x2^2*x3+x3
f3=5*x1
L={f0,f1,f2,f3}
L_3
radical ideal(L_3)

--L = toList L
L2 = LazardProjection(L,x1)