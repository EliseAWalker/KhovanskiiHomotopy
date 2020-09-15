--Example 22 from "Numerical homotopies from Khovanskii bases"
--Authors: Michael Burr, Frank Sottile, and Elise Walker

restart;
needs "Procedures.m2"; 
--This file "Procedures.m2" does the following:
---loads the packages: SubalgebraBases, PHCpack, Bertini, NumericalAlgebraicGeometry
---defines procedures for several of the algorithm steps


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
assert preservesOrder(KB, w) --checks vector w preserves grevlex order on KB

-- Compute Groebner basis for ideal I_B
wA = flatten entries (w * A);
presRing = QQ[a_1..a_#KB, MonomialOrder=>{Weights => -wA}]; 
IB = trim ker map(RVs, presRing, KB);   --this is the ideal I_B
Igens = flatten entries gens gb IB;     --this is the Groebner basis for I_B

--Compute Toric Degeneration of using Igens with parameter t
presRingt = QQ[gens presRing | {t}]
f = computeDegeneration(Igens, w*A, presRingt, t);
--f is the degeneration in weighted projective space

--Verify toric degeneration (and, consequentially, Khovanskii basis)
fzero = for i in f list sub(sub(i, t=>0), presRing); --defines special fiber
tideal = trim ideal(fzero);
LT = for i in KB list leadTerm(i);
IA = ker map(RVs,presRing, LT); --defines toric variety from semigroup
assert (IA == tideal)     --check same ideal


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
assert isIndependent(fzero_ind) 
assert isNonsingular(fzero_ind, projToricSolutions)

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


-- STEP(vi)-----------------------------------------------------------------------------
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
XLSolutions = for i in uniqueXinvLSolutions list drop(i, -2); --solutions of varphi_V(X) \cap L


