--Example 22 from "Numerical homotopies from Khovanskii bases"
--Authors: Michael Burr, Frank Sottile, and Elise Walker
restart;

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
setRandomSeed(0);
---------------------------------------------------------------------------------------

--PROCEDURES---------------------------------------------------------------------------
makeCoef = (a, b) -> (
    -- a and b are positive integers
    -- returns one list of #a lists of length #b of random complex numbers
    apply(a,(j->(apply(b, (i ->(x=random(sub(0,RR),sub(1,RR));cos(2*pi*x)+sin(2*pi*x)*ii))))))
    )

preservesOrder = (polynomialList, candidateWeight) -> (
    -- polynomialList is a list of polynomials from the same ring 
    -- candidateWeight is a row vector whose length = #generators of ring
    -- returns TRUE if candidatesWeight is a total order on each polynomial in polynomialList
    -- otherwise, returns FALSE
    R := ring polynomialList#0;
    weighted := for i in polynomialList list 
                -candidateWeight*(transpose matrix exponents i);
    flag := true;
    for i in weighted do (
      if rsort(i) != i  
      then flag = false; 
           break;
      );
    flag
    )

isIndependent = (binomialList) -> (
    -- binomialList is a nonempty list of binomials from the same ring
    -- returns true if the binomials generate the big torus and false otherwise
    -- binomialList generates the big torus if its exponent matrix is full rank
    binomialExponents := {};
    for i in binomialList do (
	ex := exponents i;
    	newex := ex#0 - ex#1;
    	binomialExponents = binomialExponents | {newex}; 
	);
    binomialExponents = transpose matrix binomialExponents;
    rank binomialExponents  == numcols binomialExponents   
    )

isNonsingular = (polynomialList, toricSolutions) -> (
    -- polynomialList is a nonempty list of binomials from the same ring
    -- toricSolutions is a list of solutions to polynomialList
    -- returns true if Jacobian(polynomialList) is full rank at each toricSolutions
    R := CC[gens ring first polynomialList];
    pList := for i in polynomialList list sub(i, R);
    flag := true; --true if nonsingular
    for i from 0 to #toricSolutions - 1 do(
	JacobianStart := sub(jacobian ideal pList, matrix{toricSolutions#i});
        if not isFullNumericalRank(JacobianStart)
	    then (flag = false; break)   
	);
    flag  
    )
---------------------------------------------------------------------------------------


--PROBLEM STATEMENT--------------------------------------------------------------------
RVs = QQ[z_1, z_2, s]; -- R(V) where valuation comes from default term order, grevlex
basisV = {s*z_1*z_2-s*z_2^2+s*z_1-s*z_2, 
          s*z_1^2-s*z_2^2+4*s*z_1-4*s*z_2, 
          s*z_2^3-6*s*z_2^2+5*s*z_2+12*s, 
          s*z_1*z_2^2-6*s*z_2^2-s*z_1+6*s*z_2+12*s, 
          s*z_1^2*z_2-6*s*z_2^2-4*s*z_1+9*s*z_2+12*s,
          s*z_1^3-6*s*z_2^2-13*s*z_1+18*s*z_2+12*s }; --vector space of functions on X
L = makeCoef(#gens RVs - 1, #basisV); --coefficients of complementary linear subspace 
-- GOAL: Compute all points in varphi_V(X) \cap L
-- METHOD: Weighted Khovanksii Homotopy
---------------------------------------------------------------------------------------


-- STEP(i) ----------------------------------------------------------------------------
-- Compute finite Khovanskii basis and valuation matrix A
KB = flatten entries sagbi(matrix {basisV}); -- Khovanskii basis
vKB = flatten for i in KB list exponents leadTerm(i); --valuations of KB
A = transpose matrix(vKB); 

-- Choose weight vector w preserving grevlex on Khovanskii basis KB
w = matrix{{-6,-5,0}};
preservesOrder(KB, w) --checks vector w preserves grevlex order on KB

-- Compute Groebner basis for ideal I_B
wA = flatten entries (w * A)
presRing = QQ[a_1..a_#KB, MonomialOrder=>{Weights => -wA}]; 
IB = trim ker map(RVs, presRing, KB);   --this is the ideal I_B
Igens = flatten entries gens gb IB;     --this is the Groebner basis for I_B

--Compute Toric Degeneration of using Igens with parameter t
presRingt = QQ[gens presRing | {t}]
f = {};
for i from 0 to #Igens-1 do {
  Bf = w * A * transpose matrix exponents Igens#i; 
  wf = -min(flatten entries Bf); 
  ex = for j in flatten entries Bf list j+wf ;
  fterms = terms Igens#i;
  f = append(f, sum apply(fterms, ex, (i,j)->sub(i,presRingt)*t^j));
} --f is degeneration in weighted proj space 

--Verify toric degeneration (and, consequentially, Khovanskii basis)
fzero = for i in f list sub(sub(i, t=>0), presRing); --defines special fiber
tideal = trim ideal(fzero);
LT = for i in KB list leadTerm(i);
IA = ker map(RVs,presRing, LT); --defines toric variety from semigroup
IA == tideal     --check same ideal


-- STEP(ii)----------------------------------------------------------------------------
f = for i in f list sub(i, {a_7=>a_7^2, a_8=>a_8^3}); --pull back homotopy to proj space


-- STEP(iii)---------------------------------------------------------------------------
CCRV = CC[drop(gens RVs, -1)]; --polynomial ring of z_1, z_2 over CC
projKodaira = {z_1^6*z_2^3, z_1^4*z_2^3, z_1^6, z_1^4, 
               z_1^2, 1, z_1^7*z_2^3, 10^(1/3)*z_1^6*z_2^4}; --Kodaira map to Y_0
--Y_0 is irreducible, so there is only one projective Kodaira map


-- STEP(iv)----------------------------------------------------------------------------
Lambda = makeCoef(2, #projKodaira); --coefficients for general complementary subspace
pbToricSystem =  apply(2,(i-> sum(apply(projKodaira,Lambda#i,(j,k)->j*k)))); --pulledback system
pbToricSolutions = solveSystem(pbToricSystem, Software=> PHCPACK);
projToricSolutions = apply(#pbToricSolutions,i->apply(projKodaira, 
	j->(if j == 1 then 1 else  sub(j,matrix{pbToricSolutions#i#Coordinates}))));
--projToricSolutions are the starting points of the homotopy

--Choose square subsystem which is  independent and nonsingular at t=0
ind = {0, 3, 5, 6, 10}; --indices of f for candidate square subsystem
isIndependent(fzero_ind)
isNonsingular(fzero_ind, projToricSolutions)

--Moving weighted degeneration to new ring for implementation in Bertini
CCpresRingtu = CC[gens presRingt | {u}];
homotopy = for i in f_ind list sub(i, CCpresRingtu); --move homotopy into new ring for Bertini
homotopy = for i in homotopy list sub(i, {t=>1-t}); --change direction of homotopy for Bertini
eqLambda = for l in Lambda list 
           fold(plus, apply(l, drop(gens CCpresRingtu, -2), (i,j)->i*j)); --equations for Lambda 
squareHomotopy = flatten append(homotopy, eqLambda);

--Calling Bertini to solve Lambda /cap Y_1
projGeneralSolutions = bertiniUserHomotopy(
    u, {t=>u}, squareHomotopy, projToricSolutions, 
    HomVariableGroup => drop(gens CCpresRingtu, -2));


-- STEP(v)-----------------------------------------------------------------------------
--Compute Y_1 \cap pr^(-1)(L) via Witness Set Homotopy
varL = drop(gens CCpresRingtu, -(#gens CCpresRingtu - #first L));
eqL = for l in L list fold(plus, apply(l, varL, (i,j)->i*j)); --linear forms defining preimage of L
gam = first flatten makeCoef(1,1); --random complex number for gamma-trick
gammaHomotopy = for i to #eqL-1 list eqLambda#i * t * gam + eqL#i * (1-t);
eqY_1 = for i in homotopy list sub(i, t=>0);
witnessHomotopy = flatten append(gammaHomotopy, eqY_1);
YinvLSolutions = bertiniUserHomotopy(
    u, {t=>u}, witnessHomotopy, projGeneralSolutions,  
    HomVariableGroup => drop(gens CCpresRingtu, -2));

--Compute (unique) points in X_1 \cap pr^(-1)(L) via projection pi
XinvLSolutions = for i in YinvLSolutions list flatten append(drop(i#Coordinates, -2), {i#Coordinates#6^2, i#Coordinates#7^3});
XinvLSolutions = sort(XinvLSolutions);
uniqueSolution = first XinvLSolutions;
uniqueXinvLSolutions = {uniqueSolution};
for i in XinvLSolutions do (
    if not areEqual(uniqueSolution, i) 
        then (uniqueXinvLSolutions = append(uniqueXinvLSolutions, i); uniqueSolution = i;)
    );

--Compute X_1 \cap L = varphi_V(X) \cap L
XLSolutions = for i in uniqueXinvLSolutions list drop(i, -2);


