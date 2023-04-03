----------------------------------
Macaulay2 Workshop at Warwick 2023
----------------------------------
# Subrings and SAGBI bases group

* Oliver Clarke (Edinburgh)
* Francesca Gandini (Slovenia)
* Parth Shimpi (Glasgow)
* Beihui Yuan (Swansea)

# Overview

We worked on implementing some new features into the SubalgebraBases package, which is currently available for Macaulay2:
* _FourTiTwo_ Strategy for sagbi
* _leadTerm_ Subring
* _NObody_ Subring - for computing Newton-Okounkov bodies
* _hilbertPolynomial_ Subring

We also worked on a computational problem proposed by Beihui, which involved computing the sagbi basis for the intersection of two subrings, for the purpose of understanding algebraic splines.

We discussed the InvariantRings package, coauthored by Francesca, and how we can combine similar datatypes (subrings).


## Helping set up M2 

There were some common questions and requests for help for installing M2 on Windows.

How to get Windows Subsystem for Linux (WSL)
**Enable WSL:**
*  Windows key + R: optionalfeatures.exe
*  Enable: 
- [X] Virtual Machine Platorm 
- [X] Windows Subsystem for Linux
* Restart computer

**Download Ubuntu:**
* Windows store
* Ubuntu 22.04.2 (works for me)
* run it

**For newer machines:**
On error, you may need WSL 2 kernel update:
https://learn.microsoft.com/en-us/windows/wsl/install-manual#step-4---download-the-linux-kernel-update-package
* Perform steps 4 and 5

# Main questions and tasks

Below are some of the main problems that were collected before and during the workshop. Note that these summaries may contain terminology that can only Ollie can understand.

## Use FourTiTwo to speed up computations
Main question: How / where can we apply FourTiTwo? There was some part of the code where we want to compare two affine semigroups (check isSAGBI).

Computing the reduction ideal when the ambient ring is a polynomial ring. 
  
* The reduction ideal is a toric ideal so we can use toricGroebner to get the Groebner basis, however we may need to check the monomial order!
* Is the weight order okay? 
* Note, we want to do eliminatiom on the reduction ideal?

## Newton-Okounkov bodies from SAGBI bases
* Which grading should be used?
  - degree grading
  - grading variable
  - user defined grading 

## Multithreaded subduction
Once we have a list of polynomials to subduct we can subduct them in parallel using Tasks and schedule

## The intersection problem for subrings
  Is there a better solution than mine?
  
  Note that a complete solution would have to work on the horrible example:
  * k[x^2, x^3, y] \cap  k[x^2, x-y]

  **Concrete statement of the intersection problem**
  Assume that S1 and S2 are   finitely generated subalgebras of the same algebra S. Find an algorithm to compute the intersection of S1 and S2.
  You may assume some or all of the following:
  * S is a polynomial ring (not a quotient)
  * S1 and S2 are homogeneous
  * S1 and S2 have finite sagbi bases, which are given
  * S1 and S2 have finite sagbi bases with respect to the same given term order
  * The intersection of S1 and S2 is finitely generated
  * The intersection of S1 and S2 has a finite sagbi basis
 
 **During the workshop**
 We discovered that there is an algorithm in [Stillman-Tsai 99] for computing the intersection of monomial algebras. We didn't have time to look into it very much.

It was also hinted (IIRC by Mike) that there should be a better way to compute intersections the subalgebras are homogeneous. It remains to check the corresponding algorithm for ideals.

## Michael's idea for top-down subduction
  Can we make it also apply to sagbi, not just isSAGBI?
* When we produce a set of S-polynomials, instead of subducting them one-by-one we can subduct away the top-degree terms and then perform Gaussian elimination on the set 

## Modified degree strategy
A 't-degree' Strategy. Given a generating set that is homogeneous with respect to a grading variable 't', can we do the Degree-By-Degree
  strategy except with respect to t and not the total degree?.

## Other theoretical questions
**Infinite / Finite certificate problem**
 Is there a finite algorithm that can determine whether (resp. or not) a finite sagbi basis exists?

**Better heuristics**
If I choose an algebra _at random_, up to what degree should I expect to check the subduction of S-polynomials?

What can we say about the heuristic in the 'Master Strategy, can it be improved sensibly?

## Hilbert polynomials and series
Given a finite sagbi basis what is the easiest way to compute the Hilbert polynomial? We can compute the Ehrhart polynomial of the NO-body, but is this really faster? Perhaps we can use the low-level fast code for computing Hilbert series?

## Substitution and maps for subrings
See substitution and maps between rings. We should have something similar for subrings.

## Beihui's algebraic spline example
Use subring intersection to verify Hilbert polynomial in the following example.

Let R = QQ[x_1, y_1, x_2, y_2] be a ring and consider the quotient ring Q = R/I where I = ideal(x_1^2,  y_2^2, x_1 - f, y_1 - g) for some polynomials f and g in R.

For example, take f = -y_2 and g = x_2 - y_2(x_2 - 1)^2.

Compute the intersection of S_1 = QQ[x_1, y_1] and S_2 = QQ[x_2, y_2] inside R. Compute a basis for the algebra by looking at the initial algebra. Can this be made to work by homogenising and using a (better) intersection algorithm for the homogeneous case?

Generalise these concepts to try and compute bases for more complicated examples where there are more patches or the graphs are different.

## Computing invariant rings
Implement the sagbi algorithm from [Stillman-Tsai] to compute the generators of invariant rings of algebraic groups. Compare this to the methods from the InvariantRings package.

## Valuations
Discussion with Diane. What should a valuation be? For subalgebras, we would ideally like the valuation on the subalgebra. So a map from S\\{0} to \RR. Todo: set up a meeting with Diane and Michael to have a chat about specifications for valuations during / before the next M2 workshop.

Question. How would this interface with the Tropical.m2 package? During the workshop, the M2 Tropical group presented a function for computing tropicalisations wrt the natural valuation on a coefficient field of Puisseux series. They are currently working on the p-adic valuation on \QQ.

## General M2 questions

**Can you make a method / function that takes no arguments?**
Yes. 
> f = method(Dispatch => Thing);
> f := L -> (...)

**What should a subring be?**
The data of a subring is really just:
* a ring Q = K[x_1 .. x_n] / I 
* some elements of Q: {f_1 .. f_m}
* and a presentation ring P = K[z_1 .. z_m]
* (this is just Subring in the SubalgebraBases package)

> [Mike paraphrased] a subring could simply be a wrapper for a map from a polynomial ring with one variable for each generator to the ambient ring containing the generators. It might be a good idea to have it as a separate package that contains only the basic functionality. Then have other packages, like _SubalgebraBases_ and _InvariantRings_, have it as a PackageExport/Import.

After a little bit of thinking, it might get a little bit messy if we try to separate the Subring type from SubalgebraBases. For example, consider subring membership. The _extrinsic method_ could (and probably should) be implemented in the Subring package so that membership can be tested.  However, in the SubalgebraBases package, we would have to overload or override it if we want to use a SAGBI basis to test membership via subduction. Alternatively, the Subring package could have a subduction-based method already implemented if a SAGBI basis is computed. But then, we're just pulling the SubalgebraBases package into the proposed Subring package. So the question is: **where is a good split for the SubalgebraBases package?** I'm not convinced there is one.





> Written with [StackEdit](https://stackedit.io/).
