--
-- second constructions:
-- add in rat.d12.g13.N-six-secants.abo-ranestad N = 1,2,...? infinity?
-- (from 2nd construction, N = 113..117.  First construction gives one of these)
-- 1 more example of Abo: elliptic surface, d=12, g=13 (need code from Hiro)
-- 1 conic bundle, deg=8 conic bundle over elliptic curve (M2 book has this example)
-- HC examples: rational, degree 11, sectionalGenus?
-- Frank's examples of rational surfaces of degree 11? Double check if we have these?
-- Sorin and Kristian wrote a paper about surfaces of degree 10.

-- need to add test for omega method

newPackage("SurfacesInP4",
    Authors => {{Name => "David Eisenbud", 
                 Email => "de@msri.org", 
                 HomePage => "http://www.msri.org/~de"},
                {Name => "Mike Stillman", 
                 Email => "mike@math.cornell.edu", 
                 HomePage => "http://pi.math.cornell.edu/~mike"}},
    Version => "0.2",
    Date => "28 March 2023",
    Headline => "Smooth surfaces in P4, not of general type",
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

export {
    "findRegularSequence",
    "Colon",
    "Random",
    "example",
    "sectionalGenus",
    "arithmeticGenus",
    "canonicalModule",
    "canonicalIdeal",
    "intersectionProduct",
    "intersectionMatrix",
    "leBarzN6",
    "surfaceInvariants",
    "Distrust",
    "surfacesInP4",
    "Genus",
    "omega",
    "randomMap",
    "randomVanishingIdeal"
    }

--SurfacesInP4#"source directory"|"SurfacesInP4/P4Surfaces.txt"

readExampleFile = method()
--beginning of each example is ---*\\s
--ending of each is beginning of next
--each example is a string or collection of strings, looking like M2 code.
--allow several lines of comments (beginning with --)

readExampleFile String := HashTable => name -> (
    filename := if fileExists name then name else SurfacesInP4#"source directory" | "SurfacesInP4/" | name;
    --filename := currentFileDirectory | "SurfacesInP4/" | name;
    --“SurfacesInP4/P4Surfaces.txt”;
    << "file: " << filename << endl;
    N := lines get filename;
    --N := lines get name;
    re := "^---+ *(.*)"; -- at least -'s, followed by spaces, then grab the last match.
    pos := positions(N, s -> match(re,s));
    indices := for p in pos list (
            m := last regex(re, N#p);
            substring(m, N#p)
            );
    hashTable for i from 0 to #pos - 1 list indices#i => (
        p := pos#i;
        concatenate between("\n", if i == #pos - 1 then
            for j from p+1 to #N-1 list N#j
        else
            for j from p+1 to pos#(i+1)-1 list N#j
        ))
    )

surfaces = readExampleFile (SurfacesInP4#"source directory"|"SurfacesInP4/P4Surfaces.txt");

example = method()
example(String, HashTable) := (ind, exampleHash) -> (
    if not exampleHash#?ind then error "example does not exist";
    trim value exampleHash#ind
    )
example String := ind -> example(ind, surfaces)

names = method()
names HashTable := (H) -> sort keys H

sectionalGenus  = method()
sectionalGenus Ideal := I -> (genera I)_1

arithmeticGenus = method()
arithmeticGenus Ideal := I -> (genera I)_0

findRegularSequence = method()
findRegularSequence Ideal := Ideal => J -> (
    --finds a random homogeneous maximal regular sequence in J of minimal
    --degree, and returns the link of J with respect to this sequence.
    S := ring J;
    if J == ideal(1_S) then return J;
    genlist := J_*;
    deglist :=  sort unique (genlist/(g -> (degree g)_0));
    D := #deglist;
    II := apply(deglist, d -> ideal select(genlist, g -> (degree g)_0 <= d));
    codims := apply(II, I -> codim I);
    levels := apply(D, i -> gens II_i * matrix basis(deglist_i, II_i));
    regseq := levels_0 * random(source levels_0, S^{codims_0:-deglist_0});
    for i from 1 to D-1 do(
	regseq = regseq | 
	         levels_i * random(source levels_i, S^{codims_i-codims_(i-1):-deglist_i}));
    regs := ideal regseq;
    assert (isHomogeneous regs);
    assert (codim regs == codims_(D-1));
    regs
    )

canonicalModule = method(Options => {Strategy => Colon})--Ext, Random, Colon})
canonicalModule Ideal := opts ->  I -> (
    S := ring I;
    n := numgens S;
    c := codim I;
    if not opts.Strategy === Ext then (
        CI := ideal take(I_*, c);
	twist := CI/degree/first//sum - n;
        if codim CI == c then return S^{twist}**((CI:I)/CI);

        << "didn't quickly find a complete intersection, using Ext..." << endl;
        );
    -- either the first c gens of I are not a CI, or the user asked to not use that method...
    Ext^(codim I)(S^1/I, S^{-n})
    )

canonicalIdeal = method(Options => {Degree=>null, Limit=>20})
canonicalIdeal Ideal := opts -> I -> (
    R := (ring I) / I;
    K := (canonicalModule I) ** R;
    H := Hom(K,R);
    if (zero H) then error("Canonical module does not inject into the homogeneous coordinate ring.");

    deg := if instance(opts.Degree, ZZ) then opts.Degree else min flatten degrees H;
    phi := homomorphism (basis (deg,H))_{0};
    tries := 1;

    -- We believe any non-zero element of Hom(K,R) should give the required injection, but we check nonetheless.
    if (kernel phi != 0) then (
        << "Warning: found a non-zero element of Hom(K,R) that is not injective"; 
        while (tries < opts.Limit) do ( 
        << "Trying random maps, after encountering " << tries << " non-injections.";
        deg = if instance(opts.Degree, ZZ) then opts.Degree else random flatten degrees H; 
        basisMap := basis(deg, H); 
        phi = homomorphism (basisMap * random(source basisMap ,R^{-deg}));
        if (kernel phi == 0) then break else tries = tries + 1;)); 

    if (tries == opts.Limit) then << "Could not find the canonical ideal after " << tries << " random tries." else
    (deg, ideal image phi))

canonicalIdeal (Ideal, Module) := opts -> (I,K) -> (
    R := (ring I) / I;
    K = K ** R;
    H := Hom(K,R);
    if (zero H) then error("Canonical module does not inject into the homogeneous coordinate ring.");

    deg := if instance(opts.Degree, ZZ) then opts.Degree else min flatten degrees H;
    phi := homomorphism (basis (deg,H))_{0};
    tries := 1;

    -- We believe any non-zero element of Hom(K,R) should give the required injection, but we check nonetheless.
    if (kernel phi != 0) then (
        << "Warning: found a non-zero element of Hom(K,R) that is not injective"; 
        while (tries < opts.Limit) do ( 
        << "Trying random maps, after encountering " << tries << " non-injections.";
        deg = if instance(opts.Degree, ZZ) then opts.Degree else random flatten degrees H; 
        basisMap := basis(deg, H); 
        phi = homomorphism (basisMap * random(source basisMap ,R^{-deg}));
        if (kernel phi == 0) then break else tries = tries + 1;)); 

    if (tries == opts.Limit) then << "Could not find the canonical ideal after " << tries << " random tries." else
    (deg, ideal image phi))

intersectionProduct = method()
intersectionProduct (Ideal, Module, Module) := ZZ => (I,M,N) -> (
    euler comodule I - euler M - euler N + euler(M**N)
)
intersectionMatrix = method()
intersectionMatrix(Ideal, List) := Matrix=> (I,L) -> (
   matrix for M in L list for N in L list intersectionProduct(I,M,N)
)

leBarzN6 = method()
leBarzN6(ZZ, ZZ, ZZ) := (d, secgenus, chi) -> (
    -- Le Barz 6-secant formula, if X is in P4.
    -- degree of a double curve of a generic projection to P3.
    delta := binomial(d-1,2) - secgenus;
    -- the number of triple points of this curve.
    t := binomial(d-1,3) - secgenus*(d-3) + 2*chi - 2;
    -- the number of apparent double points.
    -- << "t = " << t << endl;
    h := (delta * (delta - d + 2) - 3*t) // 2;
    -- N6: the value to be returned.
    - d*(d-4)*(d-5)*(d^3 + 30*d^2 - 577*d + 786) // 144
         + delta * ( 2*binomial(d,4) + 2*binomial(d,3) - 45*binomial(d,2) + 148*d - 317)
         - binomial(delta,2) * (d^2 - 27*d + 120) // 2
         - 2 * binomial(delta,3)
         + h * (delta - 8*d + 56) + t * (9*d - 3*delta - 28) + binomial(t,2)
    ) 

surfaceInvariants = method(Options => {Distrust => false})
surfaceInvariants Ideal := opts -> I -> (
     if dim I =!= 3 then error "expected the ideal of a projective surface";
     -- We assume that V(I) is smooth, but we don't check it.
     -- We compute here the canonical module, although in general it is better
     --  to avoid this, or do it elsewhere.
     R := ring I;
     n := numgens R;
     c := codim I;
     -- basics
     d := degree I;
     secgenus := (genera coker gens I)#1;
     -- pg
     KX := canonicalModule I;
--     KX = Ext^c(coker gens I, R);
--     KX = KX ** R^{-n};
     pg := numgens source basis(0,KX);
     -- q
     chi := euler I;
     q := 1-chi+pg;
--     H1O = Ext^(c+1)(coker gens I, R);
--     H1O = H1O ** R^{-n};
--     q := numgens source basis(1,H1O);
     -- chi
  --   chi := 1 - q + pg;
     -- h11.  Currently this is time consuming
     -- unless X lies in P4.
--     local K2, h11, eX;
     if n === 5 then (
	  HK := 2*secgenus - d - 2;
	  K2 := (d^2 - 10*d - 5*HK + 12*chi) // 2;
	  eX := 12*chi - K2;
	  h11 := eX - 2 + 4*q - 2*pg;
	  n6 := leBarzN6(d,secgenus,chi);
	  );
     if opts.Distrust then (
	  (eX',h11',K2') := (eX, h11, K2);
          X := Proj (R/I);
          Omega := cotangentSheaf X;
          h11 = rank HH^1(Omega);
          eX = 2 - 4*q + (2*pg + h11);
          K2 = 12*chi - eX;
	  assert ((eX',h11',K2') == (eX, h11, K2));
	  );
     
    -- << "degree    = " << d << endl;
    -- << "sectional genus = " << secgenus << endl;
    -- << "irregularity q   = " << q << endl;
    -- << "pg        = " << pg << endl;
    -- << "e(X)      = " << eX << endl;
    -- << "K^2       = " << K2 << endl;
    -- << "h11       = " << h11 << endl;
    -- << "chi       = " << chi << endl;
    -- if n === 5 then (
    --   << "N6        = " << n6 << endl;
    --   );
     if n === 5 then (
       return hashTable{{"degree",d},{"sectional genus",secgenus},
	   {"irregularity",q},{"geometric genus",pg},{"Euler number",eX},
	   {"K^2",K2},{"h^1,1",h11},{"chi",chi},{"Le Barz N6",n6}})
     else (
        return hashTable{{"degree",d},{"sectional genus",secgenus},
	   {"irregularity",q},{"geometric genus",pg},{"Euler number",eX},
	   {"K^2",K2},{"h^1,1",h11},{"chi",chi}});
     )
-*
surfacesInP4 = method(Options => {Degree=>null,Genus =>null, Type =>null})
surfacesInP4 HashTable := List => o -> (P) -> (
    N := names P;
    if o.Degree =!= null then N = select(N, k ->(	
	    R := regex("\\.d([0-9]+)\\.",k);
            if R =!= null and #R > 1 then(
               deg := value substring(R#1,k);
    	       deg == o.Degree) 
	    else false));

    if o.Genus =!= null then N = select(N, k ->(
        R := regex("\\.g([0-9]+)",k);
        if R =!= null and #R > 1 then(
           g :=  value substring(R#1,k);
           g == o.Genus)
        else false));

    if o#Type =!= null then N = select(N, k->(
	        match(o#Type, k)));
    N)
*-
--surfacesP4 = readExampleFile "./SurfacesInP4/P4Surfaces.txt"

surfacesInP4 = method(Dispatch => Thing, Options => {Degree=>null,Genus =>null, Type =>null})
surfacesInP4 Sequence := List => o -> P -> (
--    N := names P;
      N := names surfaces;
    if o.Degree =!= null then N = select(N, k ->(	
	    R := regex("\\.d([0-9]+)\\.",k);
            if R =!= null and #R > 1 then(
               deg := value substring(R#1,k);
    	       deg == o.Degree) 
	    else false));

    if o.Genus =!= null then N = select(N, k ->(
        R := regex("\\.g([0-9]+)",k);
        if R =!= null and #R > 1 then(
           g :=  value substring(R#1,k);
           g == o.Genus)
        else false));

    if o#Type =!= null then N = select(N, k->(
	        match(o#Type, k)));
    N)

omega = method()
omega(Ring, ZZ) := Module => (R, i) -> (cokernel koszul(i+2,vars R)) ** R^{i}

randomMap = method()
randomMap(Module, Module) := Matrix => (F, G) -> (
    -- Give a random graded map G --> F of degree 0.
    R := ring F;
    if R =!= ring G then error "expected modules over same ring";
    H := Hom(G,F);
    Hdeg0 := basis(0,H);
    randomf := Hdeg0 * random(source Hdeg0, R^1);
    homomorphism randomf)

randomVanishingIdeal = method()
randomVanishingIdeal(Module, Module) := Ideal => (F,G) -> (
     randomf := randomMap(F,G);
     presentIX := presentation cokernel randomf;
     sz := syz transpose presentIX;
     if numgens source sz =!= 1 then
       << "warning: expected syzygy to be a (twisted) ideal" << endl;
     ideal sz)
 randomVanishingIdeal(Matrix) := Ideal => (A) -> (
     presentIX := presentation cokernel A;
     sz := syz transpose presentIX;
     if numgens source sz =!= 1 then
       << "warning: expected syzygy to be a (twisted) ideal" << endl;
     ideal sz)

construction= new MutableHashTable
construction#"rat.d3.g0.cubicscroll"={{-1,-1},{0,0,0}}
construction#"rat.d4.g0.veronese"={{-1,-1,-1},{(omega,1)}}
construction#"rat.d5.g2.castelnuovo"={{-1,-1},{1,0,0}}
construction#"rat.d6.g3.bordiga"={{-1,-1,-1},{0,0,0,0}}
construction#"rat.d7.g4"={{-1,-1,-1,-1},{(omega,1),0}}
construction#"rat.d8.g5"={{(omega,2),(omega,2)},{(omega,1),(omega,1),0,0,0,0,0}}
construction#"rat.d8.g6"={{(omega,3)},{1,0,0,0,0}}
construction#"rat.d9.g7"={{(omega,2),(omega,3)},{(omega,1),(omega,1),0,0,0}}
construction#"rat.d9.g7"={{(omega,3),(omega,3)},{(omega,1),(omega,1),0}}
construction#"ruled.d5.g1.elliptic-scroll"={{-1,-1,-1,-1,-1},{(omega,2)}}
construction#"k3.d7.g5"={{-1,-2},{0,0,0}}
construction#"k3.d8.g6"={{-2,-1,-1},{(omega,1)}}
construction#"k3.d9.g8"={{(omega,3),-1},{0,0,0,0,0,0}}
construction#"k3.d11.g12"={{(omega,3),-1},{(omega,2),0,0}}
construction#"k3.d12.g14"={{(omega,3),(omega,3),(omega,3),(omega,3),-1},{(omega,2),(omega,2),(omega,2)}}
construction#"ell.d7.g6"={{-2,-2},{-1,-1,1}}
construction#"ell.d8.g7"={{-1,-1},{0,1,1}}
construction#"ell.d9.g7"={{(omega,2),(omega,2),-1},{(omega,1),(omega,1),(omega,1),0,0}}
construction#"ell.d10.g10"={{(omega,3),-1,-1},{(omega,1),0,0,0}}
construction#"ell.d11.g12"={{(omega,3),(omega,3),-1,-1},{(omega,1),(omega,2),0}}

createModule = method()
createModule (Ring, String) := List => (R,S) -> (if not construction#?S then error "example not in the database, sorry :(";
     P := R(monoid[getSymbol "x",getSymbol "y",getSymbol "z",getSymbol "u",getSymbol "v"]);
     L := construction#S;
     L0 := L_0;
     L1 := L_1;
     M0 := directSum(for a in L0 list(if(instance(a,ZZ)) then(P^{a}) else(omega(P,a_1))));
     M1 := directSum(for a in L1 list(if(instance(a,ZZ)) then(P^{a}) else(omega(P,a_1))));
     {M0,M1})
 
exampleGenerator = method()
exampleGenerator (Ring, String) := Ideal => (R,S) -> (if not construction#?S then error "example not in the database, sorry :(";
    M := createModule(R,S);
    mp:= randomMap(M_1,M_0);
    randomVanishingIdeal(mp))
 
-* Documentation section *-
beginDocumentation()


doc///
Key
  SurfacesInP4
Headline
  List of surfaces not of general type in P^4. 
Description
  Text
   It is known that the degrees of smooth projective complex surfaces, not of general type, embedded in P^4,
   are bounded. It is conjectured that the bound is 15, but the known bound is 80; see ***.
  Example
   surfacesInP4()
  Text
   Each example has a name consisting of the Enriques classification
   (ab = Abelian, enr = Enriques, ell = Elliptic, rat = rational, bielliptic, k3, ruled)
  Example
   I = example "enr.d11.g10";
  Text
   This is an enriques surface of degree 11 and sectional genus 10 in P4.
  Example
   degree I
   euler I
   arithmeticGenus I
   sectionalGenus I
   minimalBetti I
   K = canonicalModule I;
   H = S^1/I**S^{1};
   intersectionMatrix(I,{H,K})
   surfaceInvariants I
Contributors
  Add names!
References
  Decker, Ein, Schreyer, Constructions of surfaces in $\PP^4$, J. Alg Geom (1993)
  Decker, Schreyer, non-general type surfaces in $\PP^4$, some remarks on bounds and constructions, J. Symbolic Comp (2000)
Caveat
 Though these are supposed be examples in characteristic 0, they are actually computed in characteristic p.
 This was done in Macaulay classic, and seemed necessary because of limitations in speed, and because
 the adjunction of roots of unity was not possible there.
SeeAlso
///

///
  Key
    surfacesInP4
  Headline
    selects surfaces of given degree, sectional genus, type  
  Usage
    surfacesInP4(Degree => d, Genus => g, Type => typ)
  Inputs
    Degree => ZZ
      
  Outputs
  Description
    Text
    Example
  Caveat
  SeeAlso
///


 ///
Key
 surfacesInP4
 (surfacesInP4, HashTable)
 [surfacesInP4, Degree]
 [surfacesInP4, Genus]
 [surfacesInP4, Type]  
Headline
 selects surfaces of given degree, sectional genus, type
Usage
 L = surfacesInP4 P
Inputs
 P:HashTable
 Degree => ZZ
 Genus => ZZ
 "Type" => String
   one of "rat", "ab","k3","enr","ell","bielliptic"
Outputs
 L:List
Description
  Text
   selects surfaces of given degree, sectional genus, type   
  Example
   P = readExampleFile "P4Surfaces.txt";
   netList surfacesInP4(P, Type => "rat", Degree => 10)
SeeAlso
 names
///

 -- Type => String
 --   one of "rat", "ab","k3","enr","ell","bielliptic"


doc ///
  Key
    (sectionalGenus, Ideal)
    sectionalGenus
  Headline
    the sectional genus of a smooth surface in projective 4-space
  Usage
    sectionalGenus I
  Inputs
    I:Ideal
  Outputs
    :ZZ
  Description
    Text
      This function returns the arithmetic genus of a general linear section
      of the projective variety with ideal $I$.
    Example
      I = example "ell.d8.g7";
      betti res I
      sectionalGenus I
      degree I
      arithmeticGenus I
      surfaceInvariants I
  SeeAlso
    (arithmeticGenus, Ideal)
    (surfaceInvariants, Ideal)
    (degree, Ideal)
    (resolution, Ideal)
///

TEST ///
  S = QQ[x_0..x_5]
  R = QQ[r,s,t]
  phi = map(R, S, {r^2, r*s, r*t, s^2, s*t, t^2})
  I = ker phi
  degree I
  genera I
  assert(sectionalGenus I == 0)
  assert(degree I == 4)
///

TEST ///
  I = example "k3.d11.g11.2-sixsecants";
  betti res I
  assert(degree I == 11)
  assert(sectionalGenus I == 11)
///

doc ///
  Key
      (arithmeticGenus, Ideal)
      arithmeticGenus
  Headline
      computes the arithmetic genus of a smooth surface in projective 4-space
  Usage
      arithmeticGenus I
  Inputs
      I:Ideal
  Outputs
      :ZZ
  Description
    Text     
       This function returns the arithmetic genus of the projective variety with ideal $I$.
    Example 	
       I = example "ab.d10.g6";
       betti res I
       arithmeticGenus I
       degree I
       sectionalGenus I
       surfaceInvariants I
  SeeAlso
      (sectionalGenus, Ideal)
      (surfaceInvariants, Ideal)
      (degree, Ideal)
      (resolution, Ideal)
///

TEST ///
  I = example "bielliptic.d10.g6";
  degree I
  genera I
  assert(arithmeticGenus I == -1)
  assert(degree I == 10)
///

TEST ///
  I = example "rat.d11.g11.infty-sixsecants";
  betti res I
  assert(degree I == 11)
  genera I
  assert(arithmeticGenus I == 0)
///

doc ///
  Key
    (intersectionProduct, Ideal, Module, Module)
    intersectionProduct
  Headline
    the intersection product of two divisors inside of a smooth projective surface
  Usage
    intersectionProduct(I, M, N)
  Inputs
    I:Ideal
    M:Module
    N:Module
  Outputs
    :ZZ
  Description
    Text
      This function takes two divisors defined on a surface and returns their intersection product.
    Example
      I = example "ell.d8.g7";
      K = canonicalModule I;
      H = S^1/I**S^{1};
      intersectionProduct(I,H,K)
      intersectionProduct(I,K,K)
  SeeAlso
    (intersectionMatrix, Ideal, List)
    (arithmeticGenus, Ideal)
    (surfaceInvariants, Ideal)
    (degree, Ideal)
    (resolution, Ideal)
 ///
 
 TEST ///
    I = example "rat.d3.g0.cubicscroll";
    K = canonicalModule I;
    H = S^1/I**S^{1};
    assert(intersectionProduct(I,H,H) == 3)
    assert(intersectionProduct(I,K,K) == 8)
///

doc ///
  Key
    (intersectionMatrix, Ideal, List)
    intersectionMatrix
  Headline
    the intersection matrix of a list of divisors on a smooth projective surface
  Usage
    intersectionMatrix(I,L)
  Inputs
    I:Ideal 
      of a smooth projective surface
    L:List 
      of graded modules of the same ring as I representing divisors
  Outputs
    :Matrix
  Description
    Text
      This function calculates the intersection matrix of a list of divisors on a projective variety with ideal $I$.
    Example
      I = example "ell.d8.g7";
      K = canonicalModule I;
      H = S^1/I**S^{1};
      intersectionMatrix(I,{H,K})
  SeeAlso
    (intersectionProduct, Ideal, Module, Module)
///

TEST ///
  I = example "rat.d3.g0.cubicscroll";
  K = canonicalModule I;
  H = S^1/I**S^{1};
  M = intersectionMatrix(I,{H,K})
  assert(M == matrix{{3,-5},{-5,8}})
///

doc ///
  Key
    (surfaceInvariants, Ideal)
    surfaceInvariants
  Headline
    Invariants of a smooth surface in projective 4-space.
  Usage
    surfaceInvariants I
  Inputs
    I:Ideal 
      of a smooth projective surface
    Distrust=>Boolean
    	added check if you distrust formulas
  Outputs
    H:HashTable
  Description
    Text
      This function calculates the following invariants of a surface in projective 4-space:
      degree, sectional genus, irregularity, geometric genus, Euler number $e$, $K^2$, $h^{1,1}$,
      holomorphic Euler characteristic $\chi$ and $N_6$, the number obtained from Le Barz's six-secant formula.
    Example
      I = example "k3.d11.g11.1-sixsecant";
      surfaceInvariants I;
      arithmeticGenus I;
  SeeAlso
    (sectionalGenus, Ideal)
    (arithmeticGenus, Ideal)
    (degree, Ideal) 
    (leBarzN6, ZZ, ZZ, ZZ)
///

TEST ///
  I = example "rat.d3.g0.cubicscroll";
  assert((surfaceInvariants I)#"degree" == 3);
///

doc ///
  Key
    (leBarzN6, ZZ, ZZ, ZZ)
    leBarzN6
  Headline
    Calculates the number obtained from Le Barz's 6-secant formula.
  Usage
    leBarzN6(d,secgenus,chi)
  Inputs
    d:ZZ 
      degree of smooth projective surface
    secgenus:ZZ
        sectional genus of smooth projective surface
    chi: ZZ
        chi of smooth projective surface
  Outputs
    :ZZ
  Description
    Text
      This function calculates the number from Le Barz's six-secant formula, using the degree, sectional genus and holomorphic Euler characteristic.
    Example
      I = example "k3.d11.g11.1-sixsecant";
      surfaceInvariants I
      leBarzN6(11,11,2)
  SeeAlso
    (sectionalGenus, Ideal)
    (degree, Ideal) 
    (surfaceInvariants, Ideal)
///

TEST ///
  I = example "rat.d3.g0.cubicscroll";
  assert(leBarzN6(3,0,1) == 21);
///

doc ///
  Key
    (omega, Ring, ZZ)
    omega
  Headline
    Constructs $\Omega^i(i)$
  Usage
    omega(R,i)
  Inputs
    R:Ring
      homogeneous coordinate ring of projective 4-space
    i:ZZ
        exterior power and shift of $\Omega$
  Outputs
    M:Module
  Description
    Text
      This function calculates the $i$th exterior power of the cotangent bundle $\Omega$ with a shift of $(i)$.
    Example
      R = QQ[x,y,z,t,u];
      i = 2;
      M = omega(R,i)
  SeeAlso
    (randomMap, Module, Module)
    (randomVanishingIdeal, Module, Module)
    (randomVanishingIdeal, Matrix)
///


doc ///
  Key
    (randomMap, Module, Module)
    randomMap
  Headline
    Constructs a random graded map of degree 0
  Usage
    randomMap(M,N)
  Inputs
    M:Module
      over a ring R
    N:Module
        over a ring R
  Outputs
    A:Matrix
  Description
    Text
      This function generates a random graded map of degree 0 from N to M.
    Example
      R = QQ[x,y,z,t,u];
      M1 = R^{-1}++R^{-1}++R^{-1};
      M2 = omega(R,1);
      randomMap(M2,M1)
  SeeAlso
    (omega, Ring, ZZ)
    (randomVanishingIdeal, Module, Module)
    (randomVanishingIdeal, Matrix)
///

doc ///
  Key
    (createModule, Ring, String)
    createModule
  Headline
    the two vector bundles used in the construction of the examples of surfaces over a certain ring R
  Usage
    createModule(R,S)
  Inputs
    R:Ring
    S:String
  Outputs
    :List
  Description
    Text
      This function takes the string associated to a family of surfaces in P4 and returns the two modules used to construct an example of the family defined over that ring.
    Example
      R = ZZ/32003;
      S = "ell.d11.g12";
      M = createModule(R,S);
      X = randomVanishingIdeal(randomMap(M_1,M_0));
  SeeAlso
    (surfaceInvariants, Ideal)
    (randomVanishingIdeal, Module, Module)
    (randomVanishingIdeal, Matrix)
    (exampleGenerator, Ring, String)
 ///
 
 TEST ///
   R = ZZ/32003;
   S = "rat.d7.g4";
   M = createModule(R,S);
   X = randomVanishingIdeal(randomMap(M_1,M_0));
   assert((degree X) == 7)
///

doc ///
  Key
    (exampleGenerator, Ring, String)
    exampleGenerator
  Headline
    generates an example of a surface of the given family
  Usage
    exampleGenerator(R,S)
  Inputs
    R:Ring
    S:String
  Outputs
    :Ideal
  Description
    Text
      This function takes the string associated to a family of surfaces in P4 and returns an example in that family (defined over the given ring)
    Example
      R = ZZ/32003;
      S = "ell.d11.g12";
      X = exampleGenerator(R,S);
  SeeAlso
    (surfaceInvariants, Ideal)
    (randomVanishingIdeal, Module, Module)
    (randomVanishingIdeal, Matrix)
    (createModule, Ring, String)
 ///
 
  TEST ///
   R = ZZ/32003;
   S = "rat.d7.g4";
   X = exampleGenerator;
   assert((sectionalGenus X) == 4)
///

-* Test section *-
///
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
names P
for k in names P do elapsedTime (
    if k === "ell.d12.g14.ssue" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss2" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss1" then ( << "skipping " << k << endl; continue);
    if k === "k3.d11.g11.ss3" then ( << "skipping " << k << endl; continue);
    if k === "rat.d10.g8" then ( << "skipping " << k << endl; continue);
    << "doing " << k << endl;
    deg := null;g := null;
    I := example(k,P);
    R := regex("\\.d([0-9]+)\\.",k);
    if R =!= null and #R > 1 then
    deg = value substring(R#1,k);
    
    R = regex("\\.g([0-9]+)",k);
    if R =!= null and #R > 1 then        
    g =  value substring(R#1,k);
    assert(3 == dim I);
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    S := ring I;
    elapsedTime K = canonicalModule I;
    H = S^1/I**S^{1};
    M = elapsedTime intersectionMatrix(I,{H,K});
    print {k, deg, g, M};
    )
///
///
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
names P
elapsedTime for k in names P do elapsedTime (
    << "doing " << k << endl;
    I := example(k,P);
    S := ring I;
    J := jacobian I;
elapsedTime    singI = minors(2, J)+I;
elapsedTime c = codim singI;
    print {k, c}
    )

elapsedTime for k in names P do elapsedTime (
    << "doing " << k << endl;
    I := example(k,P);
    S := ring I;
    J := jacobian I;
elapsedTime    singI = minors(2, J)+I;
elapsedTime gbsingI := groebnerBasis (singI, Strategy => "F4");
elapsedTime c = codim ideal leadTerm gbsingI;
    print {k, c}
    )


///

TEST ///
-- This test shows some timing differences between different algorithms for canonical sheaves.
-- In general, the Ext method appears not good...
-- But the Divisor package also seems to not work (perhaps it is using Ext?)
-*
  restart
  needsPackage "SurfacesInP4"
*-
P = readExampleFile "P4Surfaces.txt";
#keys P
--P = surfacesP4;
I = example("ab.d10.g6", P)
elapsedTime K=canonicalModule(I); -- 0.0499788 seconds elapsed
elapsedTime K=canonicalModule(I, Strategy => Ext); -- 0.091749 seconds elapsed
elapsedTime K=canonicalModule(I, Strategy => Colon); -- 0.091749 seconds elapsed

I = example("ell.d12.g14.infty-sixsecants", P);
elapsedTime K=canonicalModule(I);  -- 0.597377 seconds elapsed
elapsedTime K=canonicalModule(I, Strategy => Colon);  -- 1.33254 seconds elapsed
--elapsedTime K=canonicalModule(I, Strategy => Ext); -- too long

I = example("k3.d11.g11.1-sixsecant",P);
elapsedTime K=canonicalModule(I);  -- 1.56 seconds elapsed
elapsedTime K=canonicalModule(I, Strategy => Colon);  -- 1.56 seconds elapsed
--elapsedTime K=canonicalModule(I, Strategy => Ext); -- too long

I = example("k3.d11.g11.3-sixsecants",P);
elapsedTime K=canonicalModule(I, Strategy => Colon);  -- 
elapsedTime K=canonicalModule(I);  -- 0.571776 seconds elapsed 
--elapsedTime K=canonicalModule(I, Strategy => Ext); -- 

I = example("rat.d10.g8",P);
elapsedTime K=canonicalModule(I, Strategy => Colon);  -- 0.392106 seconds elapsed
--elapsedTime K=canonicalModule(I, Strategy => Ext); 

-- The following code does not seem to work quickly.
-*
  debug needsPackage "Divisor"
  R = (ring I)/I
  elapsedTime K = canonicalDivisor(R, IsGraded=>true);
  K
  elapsedTime KM = divisorToModule K
  euler oo
  euler(KM ** KM)

  CI = ideal(I_0, I_1)
  codim CI
  S^{first degree CI_0 + first degree CI_1 - 5} ** (prune Hom(S^1/I, S^1/CI))
  euler oo
  Ext^2(S^1/I, S^{-5})
  euler oo
  res o60
*-
///

end--
-* Development section *-
restart
uninstallPackage "SurfacesInP4"
restart
installPackage "SurfacesInP4"
peek loadedFiles
restart
debug needsPackage "SurfacesInP4"
check "SurfacesInP4"
viewHelp SurfacesInP4
viewHelp

doc ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  Caveat
  SeeAlso
///



restart
debug needsPackage "SurfacesInP4"
keys surfaces

/// 
  -- degree 3.
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  assert(# surfacesInP4(Degree=>3) == 1)
  I = example first surfacesInP4(Degree=>3)
  betti res I
  surfacesInP4()
  surfaceInvariants example "ab.d10.g6"
///  

/// 
  -- degree 4
  -- 2 examples, both rational.
  --  CI(2,2)
  --  Projection of Veronese
-*
  restart
  needsPackage "SurfacesInP4"
  BUG: missing del Pezzo, degree 4. (CI(2,2))
*-  
  assert(# surfacesInP4(Degree=>4) == 2) -- incorrect currently.
  I = example first surfacesInP4(Degree=>4)
  betti res I

///  
  
/// 
  -- degree 5
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 5)-- 2 examples.
  assert(# E == 2)

  I = example E_0
  betti res I -- Castelnuovo surface: 2x2s of matrix with degrees {{1, 1, 2}, {1, 1, 2}}

  I = example E_1
  betti res I -- Ruled surface over elliptic curve

///  

/// 
  -- degree 6
-*
  restart
  needsPackage "SurfacesInP4"
  "BUG": missing k3.CI(2,3)
*-  
  E = surfacesInP4(Degree => 6) -- 1 example
  assert(# E == 1)

  I = example E_0
  betti res I -- Bordiga
///  

/// 
  -- degree 7
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 7) -- 3 examples
  assert(# E == 3)

  I = example E_0
  betti res I -- elliptic surface: 2x2s of 2x3 of degrees (1,1,3),(1,1,3)

  I = example E_1
  betti res I

  I = example E_2
  betti res I
///  

/// 
  -- degree 8
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 8) -- 4 examples
  assert(# E == 4)

  I = example E_0
  betti res I  -- 2x2s.

  I = example E_1
  betti res I -- generated by 8 quartics

  I = example E_2
  betti res I

  I = example E_3 -- divisor on cubic.
  betti res I

///  

/// 
  -- degree 9
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 9) -- 5 examples
  assert(# E == 5)

  netList for e in E list betti res example e
///  

/// 
  -- degree 10
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 10) -- 10 examples
  assert(# E == 10)

  netList for e in E list betti res example e
///  

/// 
  -- degree 11
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 11) -- 10 examples
  assert(# E == 10)

  netList for e in E list betti res example e
///  

/// 
  -- degree 12
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 12) -- 4 so far.
  assert(# E == 4)

  netList for e in E list betti res example e
///  

/// 
  -- degree 13
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 13) -- 3 so far.
  assert(# E == 3)

  netList for e in E list betti res example e
///  

/// 
  -- degree 14
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 14) -- 1 example so far
  assert(# E == 1)

  netList for e in E list betti res example e
///  

/// 
  -- degree 15
-*
  restart
  needsPackage "SurfacesInP4"
*-  
  E = surfacesInP4(Degree => 15) -- 3 so far
  assert(# E == 3)

  netList for e in E list betti res example e
///  


-- XXX

surfacesInP4 (P, Genus=>5)
surfacesInP4 (P, Type=>"ab")
surfacesInP4 (P, Type=>"ab", Genus => 21)


last surfacesInP4(P, Degree => 11)
I = example(oo, P)
minimalBetti I
netList names P
Ilist = for s in names P list s => elapsedTime example(s,P);

I = last Ilist_4;
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    K = canonicalModule I;
    H = S^1/I**S^{1};
    {k,deg,g, elapsedTime intersectionMatrix(I,{H,K})}


H = (ring I1)^{1}**comodule I1
K
intersectionProduct(I1,H,saturate image presentation(K**K))
elapsedTime saturate image presentation(K**K)


analyzeExample = k -> (
    deg := null;g := null;
    I = example(k,P);
    R := regex("\\.d([0-9]+)\\.",k);
    if R =!= null and #R > 1 then
    deg = value substring(R#1,k);
    
    R = regex("\\.g([0-9]+)",k);
    if R =!= null and #R > 1 then        
    g =  value substring(R#1,k);
    assert(3 == dim I);
    assert(deg == degree I);
    assert(g == sectionalGenus I);
    K = canonicalModule I;
    S = ring I;
    H = S^1/I**S^{1};
     {k,deg,g}
)
elapsedTime intersectionMatrix(I,{H,K})
k = "biellitic.d10.g6"
analyzeExample k
intersectionProduct(I,H,H)
intersectionProduct(I,H,K)
intersectionProduct(I,K,K)
minimalBetti K

I = example("rat.d11.g11.ssue", P)
sectionalGenus I

I = example("bordiga.d6.g3", P)
betti res I

I = example("ell.d12.g13", P)
betti res I
I = example("ell.d12.g13", P)
betti res I


I = example("rat.d5.g2.castelnuovo", P)
betti res I

I = example("veronese.d4.g0", P)
betti res I

I = example("ab.d15.g21", P)
gens ring I
betti res I
I5 = ideal submatrixByDegrees(gens I, 0, 5)
codim I5
degree I5
I5 : I
saturate I5 == I5
saturate I5 == I -- true
betti res oo

TEST ///
  for surf in {"ab.d10.g6", "bielliptic.d10.g6", "ell.d7.g6", "enr.d11.g10", "k3.d8.g6"} do (
    I := example surf ;
    invts := surfaceInvariants I; 
    expectedDim := invts#"sectional genus" - invts#"irregularity" + invts#"geometric genus"; 
    (d, J) = canonicalIdeal I;
    computedDim = numcols basis(d+1,J);
    assert (computedDim == expectedDim))
///
