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

-------------------Documentation

doc ///
  Key
    (evalPoly, RingElement, MutableHashTable)
    evalPoly
  Headline
    Evaluates the given polynomial with respect to the given sample point.
  Usage
    evalPoly(p,alpha)
  Inputs
    p:RingElement
      polynomial as a RingElement
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :RingElement
      RingElement describing the polynomial evaluated at the sample point.
  Description
    Text
      Given the polynomial (p) and sample point (alpha) it evaluates the polynomial at the sample point and returns that polynomial. This is used in the lifting phase of the CAD, where a polynomial in $k$ variables is evaluated at a point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return a univariate polynomial in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  p=x1^2*x0-2*x3*x2
	  evalPoly(p,alpha)
  SeeAlso
///

doc ///
  Key
    (evalPolyList, List, MutableHashTable)
    evalPolyList
  Headline
    Given a list of polynomials (S) and a sample point (alpha), returns the polynomials of S evaluated at alpha.
  Usage
    evalPolyList(S,alpha)
  Inputs
    S:List
      list of polynomials as RingElements
    alpha:MutableHashTable
      point described using a hash table where the keys are RingElements (variables)
  Outputs
    :List
      List of RingElements describing the polynomials in S evaluated at the sample point.
  Description
    Text
      Given the list of polynomial (S) and sample point (alpha) it evaluates the list polynomial at the sample point and returns that polynomial, by calling evalPoly on each polynomial in S. 	  This is used in the lifting phase of the CAD, where the polynomials in set of polynomials in $k$ variables are evaluated at a point $\alpha \in \mathbb{R}[x_1,\dots,\x_{k-1}] to return univariate polynomials in $\mathbb{R}[x_k]$.
    Example
	  R=QQ[x0,x1,x2,x3]
	  alpha = new MutableHashTable
	  alpha#x0 = 3
	  alpha#x1 = 4
	  alpha#x2 = 1
	  S = {x1^2*x0-2*x3*x2,x1^3*x0*x2+x3}
	  evalPolyList(S,alpha)
  SeeAlso
///

