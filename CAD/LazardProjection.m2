leadCoefficient(RingElement, RingElement) := (p, v) -> (
        d := degree(v,p);	
	contract(v^d,p)
	)
	    
LazardProjection = method()
LazardProjection(List, RingElement) := (S,v) -> (
        L1 := for p in L list leadCoefficient(p,v);		    
	L2 := for p in L list discriminant(p,v);			
	L3 := for p in subsets(L,2) list resultant(p_0,p_1,z);			    
	L1|L2|L3
	)
