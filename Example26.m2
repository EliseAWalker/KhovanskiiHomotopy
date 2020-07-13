--Example 26 from "Numerical homotopies from Khovanskii bases"
--Authors: Michael Burr, Frank Sottile, and Elise Walker

restart;
needs "Procedures.m2"; 
--This file "Procedures.m2" does the following:
---loads the packages: SubalgebraBases, PHCpack, Bertini, NumericalAlgebraicGeometry
---defines procedures for several of the algorithm steps


---------------------------------------------------------------------------------------
--PROBLEM STATEMENT--------------------------------------------------------------------
R = QQ[x,y,z, MonomialOrder=>{Weights =>{1,3,1}}];
basisV = {sub(1,R), x, y, z, x*z, y*z, x*(x*z+y), y*(x*z+y)};
L = {{ 1,  1, 1,  1,  1,  1,  1,  1 },
     { 1, -2, 3, -4,  5, -6,  7, -8 },
     { 2,  3, 5,  7, 11, 13, 17, 19 }};
F = apply(#L,(i-> sum(apply(basisV, L#i,(j,k)->j*k))));
-- GOAL: Solve F = 0
-- METHOD: SAGBI homotopy algorithm (Alg. 24)
---------------------------------------------------------------------------------------

-- STEP (i) ---------------------------------------------------------------------------
-- Compute weight w compatible with term order
B = basisV;     --SAGBI basis for CC[V] wrt term order induced by flag (see Anderson)
w = matrix {{1,1,1}};
assert preservesOrder(B, w)

--STEP (ii) ---------------------------------------------------------------------------
-- Degenerate SAGBI basis elements
Rt = QQ[gens R | {t}];
Bt = computeDegeneration(B, w, Rt, t);

--STEP (iii) --------------------------------------------------------------------------
-- Degenerate system F
Ft = apply(#L, (i-> sum(apply(Bt, L#i, (j,k)->j*k))));

--STEP (iv) ---------------------------------------------------------------------------
-- Solve sparse system
startSystem = for i in Ft list sub(i, t=>0);
CCR = CC[gens R];
startSystem = for i in startSystem list sub(i, CCR); --move to correct ring for PHCpack
startSystemSolutions = solveSystem(startSystem, Software => PHCPACK);

--STEP (v) ----------------------------------------------------------------------------
-- Moving degeneration Ft to new ring for implementation in Bertini
homotopy = for i in Ft list sub(i, {t=>1-t}); --switch direction for Bertini
CCRtu = CC[gens Rt |{u}];
GammaHomotopy = applyGammaTrick(CCRtu, homotopy); --apply Gamma trick
targetSystemSolutions = bertiniUserHomotopy(u, {t=>u}, GammaHomotopy, startSystemSolutions);
