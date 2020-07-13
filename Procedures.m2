--Procedures for the Khovanskii homotopy
--Refer to: "Numerical homotopies from Khovanskii bases"
--Authors: Michael Burr, Frank Sottile, and Elise Walker


--PACKAGES----------------------------------------------------------------------------
needsPackage "SubalgebraBases" 
-- The "SubalgebraBases" package computes SAGBI bases and can be found at:
-- https://github.com/Macaulay2/M2/tree/master/M2/Macaulay2/packages/SubalgebraBases
--
needsPackage "PHCpack"
-- The "PHCpack" package performs the polyhedral homotopy. Information available at:
-- https://faculty.math.illinois.edu/Macaulay2/doc/Macaulay2-1.15/share/doc/Macaulay2/PHCpack/html/
--
needsPackage "Bertini"
-- The "Bertini" package performs user-defined homotopies. Information available at:
-- http://www2.macaulay2.com/Macaulay2/doc/Macaulay2-1.15/share/doc/Macaulay2/Bertini/html/index.html
--
needsPackage "NumericalAlgebraicGeometry"
---------------------------------------------------------------------------------------


--PROCEDURES---------------------------------------------------------------------------
--Returns a list of lists of random unit complex numbers
makeCoef = (a, b) -> (
    -- a and b are positive integers
    -- returns one list of #a lists of length #b of random complex numbers
    apply(a,(j->(apply(b, (i ->(x=random(sub(0,RR),sub(1,RR));cos(2*pi*x)+sin(2*pi*x)*ii))))))
    )

--Determines if a given weight is compatible with the monomial order on
--a list of polynomials
preservesOrder = (polynomialList, candidateWeight) -> (
    -- polynomialList is a list of polynomials from the same ring 
    -- candidateWeight is a row vector whose length = #generators of ring
    -- returns TRUE if candidateWeight totally orders each polynomial in polynomialList
    -- otherwise, returns FALSE
    R := ring polynomialList#0;
    weighted := for i in polynomialList list 
                -candidateWeight*(transpose matrix exponents i);
    for i in weighted do (
      if rsort(i) != i  
        then (print "weight doesn't preserve order"; return false;);
      if #(unique flatten entries i) != #(flatten entries i)
        then (print "weight doesn't break ties"; return false;);     
      );
    return true;
    )

--Computes weighted toric degeneration of a list of polynomials
computeDegeneration = (polynomialList, weight, degenerationRing, t) -> (
    --polynomialList is the list of polynomials to be degenerated
    --weight is the weight for the degeneration
    --degenerationRing is the ring with generators containing the variables
    --  in polynomialList as well as the degeneration variable t
    apply(polynomialList, i-> (
        weightDotexponent = weight * transpose matrix exponents i;
        wf = -min(flatten entries weightDotexponent);
        degenerationExponents = for j in flatten entries weightDotexponent list j+wf;
        polynomialTerms = terms i;
        sum apply(polynomialTerms, degenerationExponents, 
                    (j,k)-> sub(j, degenerationRing)*t^k)
        )
        )
    )

--Determines if the exponents b of list of binomials, x^b = 1, are linearly independent
isIndependent = (binomialList) -> (
    -- binomialList is a nonempty list of binomials from the same ring
    -- returns true if the binomials generate the big torus and false otherwise
    -- binomialList generates the big torus if its exponent matrix is full rank
    binomialExponents := {};
    binomialExponents = apply(binomialList, i->(
        ex = exponents i;
        ex#0 - ex#1
        ));
    binomialExponents = transpose matrix binomialExponents;
    rank binomialExponents  == numcols binomialExponents   
    )

--Determines if a system of polynomials is nonsingular at a set of points
isNonsingular = (polynomialList, toricSolutions) -> (
    -- polynomialList is a nonempty list of binomials from the same ring
    -- toricSolutions is a list of solutions to polynomialList
    -- returns true if Jacobian(polynomialList) is full rank at each toricSolutions
    R := CC[gens ring first polynomialList]; --move ring over complex numbers
    pList := for i in polynomialList list sub(i, R); --move polynomials to new ring
    for i from 0 to #toricSolutions - 1 do(
        JacobianStart := sub(jacobian ideal pList, matrix{toricSolutions#i});
        if not isFullNumericalRank(JacobianStart)
            then return false;   
        );
    return true; 
    )

--Adapts a homotopy in t to include the gamma-trick
applyGammaTrick = (complexRing, polynomialList)-> (
    -- Returns homotopy set up for gamma trick
    -- Assumes path variable t 
    -- Assumes polynomialList are in a ring over QQ, say with generators X
    -- Assumes complexRing is over CC with generators {X,u}
    S := QQ[gens ring first polynomialList| {u}]; --temporary ring for gamma-sub.
    newHomotopy := for i in polynomialList list sub(i, S);
    newHomotopy = for i in newHomotopy list 
        (u*t + 1-t)^degree(t,i)*sub(i, t=>u*t/(u*t + 1-t)); --polynomial over 1
    newHomotopy = for i in newHomotopy list numerator i;    --polynomial
    newHomotopy = for i in newHomotopy list sub(i, complexRing);
    use complexRing;
    gam := - .622126 + 1.95967*ii; --complex number for gamma trick
    newHomotopy = for i in newHomotopy list sub(i, u=> gam);
    newHomotopy
    )
---------------------------------------------------------------------------------------
