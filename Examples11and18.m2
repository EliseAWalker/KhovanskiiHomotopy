--Examples 18 and 11 from "Numerical homotopies from Khovanskii bases"
--Authors: Michael Burr, Frank Sottile, and Elise Walker

restart;
needs "Procedures.m2"; 
setRandomSeed(9);
--This file "Procedures.m2" does the following:
---loads the packages: SubalgebraBases, PHCpack, Bertini, NumericalAlgebraicGeometry
---defines procedures for several of the algorithm steps

---------------------------------------------------------------------------------------
--PROBLEM STATEMENT--------------------------------------------------------------------
RVs = QQ[X,Y,Z,s,  MonomialOrder=>{Weights =>{1,1,1,0}, {0,0,1,0},{0,1,0,0},{1,0,0,0}}];
basisV = {1*s, X*s, Y*s, Z*s, X*Z*s, Y*Z*s, X*(X*Z+Y)*s, Y*(X*Z+Y)*s};
L = {{ 1,  1, 1,  1,  1,  1,  1,  1 },
     { 1, -2, 3, -4,  5, -6,  7, -8 },
     { 2,  3, 5,  7, 11, 13, 17, 19 }}; --coefficients of complementary linear subspace
-- GOAL: Compute all points in varphi_V(X) \cap L
-- METHOD: Khovanskii homotopy algorithm (14), which calls the toric two-step homotopy 
--         algorithm (3)
---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------
--ALGORITHM 14------------------------------------------------------------------------- 
-- INPUT ---------------------------------------------------------------------------
--Compute finite Khovanskii basis and valuation matrix A
KB = basisV; -- finite Khovanskii basis computed by Anderson
inKB = {1*s, X*s, Y*s, Z*s, X*Z*s, Y*Z*s, X*Y*s, Y*Y*s}; --initial algebra
A = transpose matrix flatten for b in inKB list exponents b; 


-- STEPS (i-iii) ----------------------------------------------------------------------
--Choose weight vector w so the w-minimal terms of KB correspond to inKB
w = matrix{{1,1,1,-2}};
assert preservesOrder(KB,w) -- checks w satisfies desired property

--Compute Groebner basis for ideal I_B
wA = flatten entries (w*A);
presRing = QQ[x_0..x_(#KB -1), MonomialOrder=>{Weights=>-wA}]
IB = ker map(RVs, presRing, KB); --ideal for phi_V(X)
Igens = flatten entries gens gb IB; --this is a Groebner basis for I_B


-- STEP (iv) --------------------------------------------------------------------------
--Compute Toric Degeneration (G_t) of using Igens with parameter t
presRingt = QQ[gens presRing | {t}]
f = computeDegeneration(Igens, w*A, presRingt, t);
--f is now G_t, i.e. defines the toric degeneration

--Verify toric degeneration (and, consequentially, Khovanskii basis)
fzero = for i in f list sub(sub(i, t=>0), presRing); --defines special fiber
tideal = trim ideal(fzero);
IA = ker map(RVs,presRing, inKB); --defines toric variety from semigroup
assert (IA == tideal)     --check same ideal


-- STEP (v) -------------------------------------------------------------------------
--Construct Kodaira map for toric variety at t=0
CCRV = CC[drop(gens RVs, -1)]; --polymomial ring of x,y,z over CC
projKodaira = for i in inKB list sub( sub(i, s=>1), CCRV);


-- STEP (vi) ------------------------------------------------------------------------
-- Applying Algorithm 3



---------------------------------------------------------------------------------------
--ALGORITHM 3--------------------------------------------------------------------------
eqL = apply(#L,(i-> sum(apply(gens presRing, L#i,(j,k)->j*k)))); --equations defining L
-- STEP (i) ---------------------------------------------------------------------------
-- Compute pull back of toric system and L
pbToricSystem = apply(#L,(i-> sum(apply(projKodaira, L#i,(j,k)->j*k))));

-- STEP (ii) --------------------------------------------------------------------------
-- Solve pulled back system using the polyhedral homotopy
pbToricSolutions = solveSystem(pbToricSystem, Software=> PHCPACK);

-- STEP (iii) -------------------------------------------------------------------------
-- Push forward pulled back solutions
projToricSolutions = apply(#pbToricSolutions,i->apply(projKodaira, 
      j->(if j == 1 then 1 else  sub(j,matrix{pbToricSolutions#i#Coordinates}))));

-- STEP (iv) --------------------------------------------------------------------------
--Choose square subsystem which is independent and nonsingular at t=0
ind = {6, 7, 8, 9}; --indices of f for candidate square subsystem
assert isIndependent(fzero_ind)
assert isNonsingular(fzero_ind, projToricSolutions)

--Moving weighted degeneration to new ring for implementation in Bertini
CCpresRingtu = CC[gens presRingt | {u}];
squareHomotopy = flatten {f_ind, eqL};
homotopy = for i in squareHomotopy list sub(i, CCpresRingtu); --move into new ring for Bertini
homotopy = for i in homotopy list sub(i, {t=>1-t}); --change direction of homotopy for Bertini

--Calling Bertini to solve varphi(X) \cap L 
projSolutions = bertiniUserHomotopy(
    u, {t=>u}, homotopy, projToricSolutions, 
    HomVariableGroup => drop(gens CCpresRingtu, -2));



