-- -*- coding: utf-8 -*-

newPackage(
	"KoszulSummands",
	Version => "0.1",
	Date => "October, 2022",
	AuxiliaryFiles => false,
	Authors => {{Name => "Daniel Rostamloo", Email => "drostamloo@berkeley.edu"},
	    {Name => "David Eisenbud", Email => "de@math.berkeley.edu"}},
	Headline => "Determining Socle Summands Property in Koszul resolutions of Artin Local Rings",
	PackageExports => {"Points", "DGAlgebras", "MonomialOrbits", "SocleSummands"},
	DebuggingMode => true)
    
export{
    "koszulIdeals", -- given an ideal, return a list of syzygies given by the matrices of the associated Koszul complex
    "koszulSS", -- given an ideal, return a list of which syzygies from its Koszul complex have socle summands
    "randomBinomialIdeals", -- generate random binomial ideals with specific generator degrees, number, and indeterminates
    "killCycleComplexes", -- given a ring, an ideal, and an integer, return a list of Koszul complexes made exact by killing cycles up to homological degree equaling the given integer
    "complexSocSummands", -- given an arbitrary chain complex, return a list of which syzygies have socle summands
    "separateDiffs", -- given a chain complex K2 and another chain complex K1 which is its summand in the first coordinate, return the boundary maps of K2 with the source restricted to the columns of K2 not included in K1
    "originalDiffs", -- given a chain complex K2 and another chain complex K1 which is its summand in the first coordinate, return the boundary maps of K2 with the source restricted to the columns of K1
    "subrows", -- like the method submatrix, but for choosing a subset of rows instead of columns
    "restrictTarget", -- similar to separateDiffs, except the target of the boundary maps of K2 are restricted to K1
    "cycleSummands" -- fixes the socleSummands method for chain complexes from the SocleSummands package
    }


koszulIdeals = method()
koszulIdeals(Ring) := (R) -> (
    K := koszulComplexDGA R;
    complex := toComplex K;
    matrices := apply(length complex, i -> complex.dd_(i+1));
    apply(matrices, ker)
    )

koszulSS = method()
koszulSS(Ring) := (R) -> (
    K := koszulIdeals(R);
    L := for i in toList(0..length K - 1) list if hasSocleSummand(K_i) then i+2 else continue
    )

isSocAlg = method()
isSocAlg(Ring, Ideal) := (S, I) -> (
    mS := ideal vars S;
    R := S/I;
    n := numgens R;
    mmR := ideal vars R;
    K := koszulComplexDGA R;
    L := toComplex K;
    A := K.natural;
    soc := apply(n, i-> gens ((0_R*L_(i+1)):mmR));
    cyc := apply(n, i-> syz K.dd_(i+1));
    socSummands := apply(n, i-> soc_i%(vars R**cyc_i));
    
    alg := apply(n, j -> apply(n, i -> ((dgAlgebraMultMap(K,A_j))_(i+1)*socSummands_i)));

    inj := apply(n, j -> apply(n-1, i -> (alg_j)_i % (vars R**cyc_(i+1))));
    
    surj := apply(n, j -> apply(n-1, i -> (alg_j)_i // socSummands_(i+1)));
    
    )

-- new method: only need to check the image of the socles in the homology
-- idea: soc % image =/= 0 implies (maximal) socle summand

isSocAlgebra = method()
isSocAlgebra(Ring, Ideal) := (S, I) -> (
    mS := ideal vars S;
    R := S/I;
    n := numgens R;
    mmR := ideal vars R;
    K := koszulComplexDGA R;
    L := toComplex K;
    A := K.natural;
    soc := apply(n, i-> gens ((0_R*L_(i+1)):mmR));
    cyc := HH K;
    socSummands := apply(n, i-> soc_i // HH_i)
)

-*
killedCycleSummands = method()
killedCycleSummands(Ring, Ideal) := (S, I) -> (
    n := numgens S;
    R := S/I;
    K := koszulComplexDGA R;
    
    K1 := killCycles(K, EndDegree => 1);
    K2 := killCycles(K1, EndDegree => 2);
    K3 := killCycles(K2, EndDegree => 3);
    K4 := killCycles(K3, EndDegree => 4);
    K5 := killCycles(K4, EndDegree => 5);
    K6 := killCycles(K5, EndDegree => 6);
    
    C := toComplex(K6, 6);
 
    cyc := apply(6, i -> syz C.dd_(i+1));
    L := for i in toList(0..5) list if hasSocleSummand(image cyc_i) then i+2 else continue
)
*-

killCycleComplexes = method()
killCycleComplexes (Ring, Ideal, ZZ) := (S, I, m) -> (
    n := numgens S;
    R := S/I;
    K := koszulComplexDGA R;
    K' := K;
    
    KK := for i from 0 to m list (
	if i==0 then K' else K' = killCycles(K', EndDegree => i));
    
    C := KK / (K -> toComplex(K, 5))
)

randomBinomialIdeals = method()
randomBinomialIdeals(Ring, ZZ, ZZ, ZZ) := (R, maxdeg, maxnumgen, numideals) -> (     
           mm := ideal gens R;
	   
	   for j from 1 to numideals list(
	       ideal for i from 1 to random(1, maxnumgen) list(
		   d := random maxdeg;
	   	   mmd := (mm^d)_*;
		   t := #mmd;
		   m1 := mmd_(random t) * mmd_(random t);
		   m2 := mmd_(random t) * mmd_(random t);
		   b := m1-m2))
	   )
       
complexSocSummands = method()
complexSocSummands(ChainComplex) := (K) -> (
    cyc := for i from 1 to length K list syz K.dd_i;
    for i from 1 to length K-1 list if hasSocleSummand(image cyc_i) then i+2 else continue
    )
		  	  
separateDiffs = method()
separateDiffs(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    ddiffs := apply(length K2-1, i -> submatrix(d2_(i+1), toList(numcols d1_(i+1) .. numcols d2_(i+1) - 1)))
)

restrictTarget = method()
restrictTarget(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    restricted := apply(length K2-1, i -> subrows(d2_(i+1), toList(0 .. numrows d1_(i+1) - 1)))
)

subrows = method()
subrows(Matrix, List) := (M, rows) -> (
    transpose submatrix(transpose M, rows)
)

originalDiffs = method()
originalDiffs(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    ddiffs := apply(length K2-1, i -> submatrix(d2_(i+1), toList(0 .. numcols d1_(i+1) - 1)))
)

cycleSummands = method(Options => {Verbose => false})
cycleSummands(ChainComplex) := o -> K -> (
    c := length K;
    mm := ideal gens ring K;
    cycles := for i from 1 to c list image syz K.dd_i;
    for i from 1 to c list socleSummands(cycles_(i-1), o)
)    

beginDocumentation()

doc ///
    	Key
	    	koszulIdeals
		(koszulIdeals, Ring)
	Headline
	    	Returns the list of syzygies (as matrices) from the Koszul complex of a given ring
	Usage
	    	koszulIdeals R
    	Inputs
	    	R:Ideal
		    	An ring R
	Outputs
	    	:List
		    	List of syzygies from the Koszul complex
	Description
	    	Text
		    	Takes a ring and returns a list of syzygies from the associated Koszul complex.
		Example  
		        S = ZZ/1993[a,b,c]
		        I = ideal("a4,b4,c4,ab3,a2c2")
	                koszulIdeals S/I
		
///


doc ///
    	Key
	    	koszulSS
		(koszulSS, Ring)
	Headline
	    	Returns a list of syzygies having socle summands
	Usage
	    	koszulSS I
	Inputs
	    	R:Ideal
		    	A ring
	Outputs
	    	:List
		    	List of indices corresponding to syzygies having socle summands
	Description
	    	Text
		    	given a ring, return a list of which syzygies from its Koszul complex have socle summands
		Example
		    	S = ZZ/1993[a,b,c]
			I = ideal("a4,b4,c4,ab3,a2c2")
			koszulSS S/I

///


doc ///
    	Key
	        randomBinomialIdeals
		(randomBinomialIdeals, Ring, ZZ, ZZ, ZZ)
	Headline
	    	Returns a random list of homogeneous binomial ideals
	Usage
	    	randomBinomialIdeals(R, maxdeg, maxnumgen, numideals)
	Inputs
	    	R:Ring
		    	The ambient ring of the binomial ideals
		maxdeg:ZZ
		    	The maximal degree of any homogeneous binomial generator
		maxnumgen:ZZ
		    	The maximal number of binomial generators for any ideal
		numideals:ZZ
		    	The desired number of random binomial ideals in the list
	Outputs
	    	:List
		    	List of random binomial ideals
	Description
	    	Text
		        Returns a random list of a specified number of homogeneous binomial ideals of a given ring with generators of a specified maximum degree and a maximum number of such generators
		Example
		    	S = ZZ/101[a,b,c]
			randomBinomialIdeals(S, 3, 4, 5)

///


doc ///
    	Key
	        killCycleComplexes
		(killCycleComplexes, Ring, Ideal, ZZ)
	Headline
	    	Returns a list of Koszul-type complexes made sequentially exact by killing cycles
	Usage
	    	killCycleComplexes(S, I, m)
	Inputs
	    	S:Ring
		    	The underlying ring of the Koszul complexes
		I:Ideal
		    	The ideal yielding the Koszul complexes
		m:ZZ
		    	The upper bound on homological degree for making the Koszul complexes exact
	Outputs
	    	:List
		    	List of Koszul-like complexes, increasing in exactness up to homological degree specified by m
	Description
	    	Text
		        Given a ring, an ideal, and an integer, return a list of Koszul complexes made exact by killing cycles up to homological degree equaling the given integer
		Example
		    	S = ZZ/101[a,b,c]
			I = ideal (a^4, b^5, c^3, d^6)
			killCycleComplexes(S, I, 4)
			
///
			
doc ///
    	Key 
	        complexSocSummands
	        (complexSocSummands, ChainComplex)
	Headline
	    	Returns a list of indices corresponding to syzygies of a chain complex having socle summands
	Usage
	    	complexSocSummands(K)
	Inputs
	    	K:ChainComplex
		    	A chain complex
	Outputs
	    	:List
		    	List of indices describing syzygies of the complex having socle summands
	Description
	    	Text
		    	Given a chain complex, return a list of indices specifying syzygies which have socle summands
		Example
		    	S = ZZ/101[a,b,c]
			I = ideal (a^4, b^5, c^3, d^6)
			K = 
///

end--

S = ZZ/(101)[a..d]
I = ideal (a^4, b^5, c^3, d^6);
J = compress (gens ((ideal vars S)^4) % I);

-- nxn minors Golod ideal case
P = ZZ/(101)[x,y];
A = matrix{{x^2,x*y,y^4,y*x^2},{x*y^7,x^4,y^3,x^3+y},{x^3*y,x^2*y^4,y^2,x^2-y},{x^2,y^3,x*y,x^2-y},{y^2-x^2,y^3-x,x*y-x^2,y^5}};
I = minors(3,A);
isGolod(P/I)

-- Toric ideal case
A=matrix{{2,1,4,5},{1,2,1,0},{0,2,0,1}};
T = toricIdeal(A, S)

R= P/I

koszulSS(R)
kSS(P/I, 6)

-- To do: decrease -5 until finding a nonBurch Golod ring
L = orbitRepresentatives(S, I, monomialIdeal J, -5); #L

elapsedTime tally for i in L_{0..1000} list koszulSS(S/i)
elapsedTime tally for i in L_{0..1000} list kSS(S/i, 6)

elapsedTime tally for i in L list koszulSS(S/i)
elapsedTime tally for i in L list kSS(S/i, 6)

select(L, l -> koszulSS(S/l)_0 == 0);

-- Conjecture 1: Every Burch ring has socle summands in every Koszul cycle after 2

G = select(L, l -> isGolod(S/l)); #G	

-- To do: Randomly generate almost complete intersections, i.e. ideals with n+1 (for n vars) homogeneous generators all of the same degree, see how many are Golod. How many are Burch?

R = ZZ/(101)[x,y,z];
L = for i in toList(20..1000) list randomBinomialIdeal(apply({i/10, i/10, i/10, i/10}, ceiling), R);
elapsedTime tally for i in L list isBurch(i)
elapsedTime tally for i in L list isGolod(R/i)

G = select(L, l -> isGolod(R/l) and not isBurch(l));
elapsedTime tally for i in G list koszulSS(R/i)
elapsedTime tally for i in G list kSS(R/i, 5)


-----------------
loadPackage ("SocleSummands", Reload => true)
loadPackage ("MonomialOrbits", Reload => true) 
loadPackage ("Binomials", Reload => true)
loadPackage ("KoszulSummands", Reload => true)
S = ZZ/101[a,b,c]
mS = ideal vars S
R = S/(mS^3)


n = numgens R
mmR = ideal vars R
K = koszulComplexDGA R
L = toComplex K
A = K.natural
vars A
soc = apply(n, i-> gens ((0_R*L_(i+1)):mmR))
soc_0
K.dd
cyc = apply(n, i-> syz K.dd_(i+1))
socSummands = apply(n, i-> soc_i%(vars R**cyc_i))
socSummands_0
prune image socSummands_1
soc_1
target socSummands_0

cyc_0*(soc_0//cyc_0)
soc_0%(vars R ** cyc_0)
-- what is the purpose of this?

(dgAlgebraMultMap(K,A_1))_1*socSummands_0
((dgAlgebraMultMap(K,A_1))_1*socSummands_0)%(vars R **cyc_1)
(dgAlgebraMultMap(K,A_1))_2

inj0 = ((dgAlgebraMultMap(K,A_0))_1*socSummands_0)%(vars R **cyc_1)
inj1 = ((dgAlgebraMultMap(K,A_1))_1*socSummands_0)%(vars R **cyc_1)
inj = inj0 || inj1
ker inj

surj0 = ((dgAlgebraMultMap(K,A_0))_1*socSummands_0) // socSummands_1
surj1 = ((dgAlgebraMultMap(K,A_1))_1*socSummands_0) // socSummands_1
surj = surj0 | surj1
coker surj

-- what is going on with indexing here? why reduce by cyc again in the second line?
-- Reduce by cyc in the second line to check whether we get a nonzero socle summand

(dgAlgebraMultMap(K,A_1))_1*soc_0

ker inj0
ker inj1

ring A_1
ring A_2

source (dgAlgebraMultMap(K,A_0))_1
M1 = image((dgAlgebraMultMap(K,A_0))_1*socSummands_0)
M2 = image((dgAlgebraMultMap(K,A_1))_1*socSummands_0)
A_2
-- rank issue: M2 does not have the same rank as M1: fixed

dom1 = (image soc_0)^2
tar1 = image soc_1
surjMap = matrix {{A_0, A_0, A_0, A_0}, {A_1, A_1, A_1, A_1}}

map1 = map(dom1, tar1, surjMap)

dom2 = image socSummands_0
tar2 = (image socSummands_1)^2

-- another question: surjectivity on socles implies surjectivity of socle summands, so does it suffice for us to check the second one only?

-- now doing socle summand experiments with augmented algebra resolution syzygies and koszul cycles
kk = ZZ/(101)
S = kk[a..d]
S' = kk[b..d]
project = map (S', S)
I = ideal"a2b3,b4c3,c4,a3d2"
J = compress (gens ((ideal vars S)^3) % I);

B = randomBinomialIdeals(S,3,4,10); #B

elapsedTime tally for i in B list not isBurch(i)
elapsedTime tally for i in B list not isGolod(S/i)
elapsedTime G = select(B, l -> not (isGolod(S/l) or isBurch(l))); #G
G / minimalBetti
H = apply(G, i -> i + ideal"a")
H / minimalBetti
G' = G / project
G' / minimalBetti    
G' / isBurch
G' / isGolod
for i in G' list isGolod(S'/i)
koszulSS(S'/G')
killedCycleSummands(S', G')

elapsedTime tally for i in G list koszulSS(S/i)
elapsedTime tally for i in G list killedCycleSummands(S, i)

n = numgens S;
R = S/G_0;
K = killedCycleSummands(S, G_0, 2);
K
cycs = K / complexSocSummands;
cycs

K = koszulComplexDGA R;

K' = K;
m = 2;

KK = for i from 0 to m list (
	if i == 0 then K' else K' = killCycles(K', EndDegree => i));
    
JJ = KK / (i -> toComplex(i, 6));
JJ / betti
minimalBetti G_1

cycs = for i from 1 to #KK list 
L = for i in toList(0..5) list if hasSocleSummand(image cyc_i) then i+2 else

C = toComplex(K6, 6)


cyc = apply(6, i -> syz C.dd_(i+1)); #cyc
L = for i in toList(0..5) list if hasSocleSummand(image cyc_i) then i+2 else continue

L = orbitRepresentatives(S, I, monomialIdeal J, -3); #L

elapsedTime tally for i in L list not isBurch(i)
elapsedTime tally for i in L list isGolod(S/i)
elapsedTime H = select(L, l -> not (isGolod(S/l) or isBurch(l))); #G

elapsedTime tally for i in L list koszulSS(S/i)
elapsedTime tally for i in L list killedCycleSummands(S, i)

koszulSS(S/L_20)
killedCycleSummands(S, L_20)

------------------------------------------------------------------------------------
loadPackage ("SocleSummands", Reload => true)
loadPackage ("MonomialOrbits", Reload => true) 
loadPackage ("KoszulSummands", Reload => true)

-- Question: in the Burch case, how are socle summands presented in the second homological degree (and onwards) (and what are their internal degrees?)

kk = ZZ/(101);
S = kk[a..d];

-- generate Burch monomial ideals
I = ideal"a4, b4, c4, d4"
-- J = compress (gens ((ideal vars S)^3) % I);
L = orbitRepresentatives(S, I, (3,4,5)); #L
B = select(L, l -> isBurch(l)); #B

-- Build complexes
KK = killCycleComplexes(S, B_0, 3);
K = koszulComplexDGA(S/B_0)
dgKK = killCycles(K, EndDegree => 1)
L = toComplex(K)
L1 = toComplex(dgKK, 4)

netList apply(length L + 1, i -> L.dd_i)
netList apply(length L1 + 1, i-> L1.dd_i)

degreeLength dgKK.natural
flatten entries vars dgKK.natural / degree

socleSummands(KK_0)
SocKK = socleSummands(KK_0, Verbose => true)
SocKK = KK / (k -> socleSummands(k, 4, Verbose => true)
betti KK_1
betti KK_0
socle (S/B_0)^1

J = (ideal vars S)^3;


-- Many examples 
big = for i in B_{0..5} list (
    KK = killCycleComplexes(S, i, 3);
    bigSoc = KK / socleSummands
    )

betti KK_0
betti KK_1
socleSummands(KK_0, Verbose => true)

(B_5 : ideal vars S)

B_0

-* 
Separating differentials according to killed cycles, chasing socle summands
*-

kk = ZZ/(101);
S = kk[a..c];

-- generate Burch monomial ideals
I = ideal"a5, b5, c5"
-- J = compress (gens ((ideal vars S)^3) % I);
L = orbitRepresentatives(S, I, (3,4)); #L
B = select(L, l -> isBurch(l)); #B
B_0

-- Build complexes
KK = killCycleComplexes(S, B_0, 3);
K = koszulComplexDGA(S/B_0)

-- Separate differentials

length KK_2
diffs = separateDiffs(KK_0, KK_3);
ring diffs_1 === ring KK_0

lif = map(ring KK_0, S)

pushForward(lif, diffs_1)

SocKK0 = cycleSummands(KK_0)
SocKK2 = cycleSummands(KK_3)

apply(diffs, i -> socleSummands(image syz i))
numcols diffs_2
numrows diffs_2

KK_1
(KK_0).dd_2
(KK_1).dd_2
(KK_1).dd_3
(KK_1).dd_3

diffs_1

-* 
Now test the "socle summand persistence" behavior in the killed cycles exact sequence
*-

kk = ZZ/(101);
S = kk[a..c];

-- generate Burch monomial ideals
I = ideal"a5, b5, c5"
-- J = compress (gens ((ideal vars S)^3) % I);
L = orbitRepresentatives(S, I, (3,4,5)); #L
B = select(L, l -> isBurch(l)); #B
B_0
prune socle ((ring B_0)^1 / B_0)
-- Build complexes
KK = killCycleComplexes(S, B_0, 4);
K = koszulComplexDGA(S/B_0)

-- Separate differentials, restricting target to the summand koszul complex
restricted = restrictTarget(KK_0, KK_1);
ring restricted_0 === ring KK_0

cycleSummands(KK_0, Verbose => false)
cycleSummands(KK_1)

apply(restricted, i -> betti i)
apply(restricted, i -> socleSummands(image syz i, Verbose => false))
syz restricted_3

restricted_1
(KK_3).dd_2

-- do we need to go deeper?

KK = killCycleComplexes(S, B_0, 4);

restricted = restrictTarget(KK_0, KK_4);
ring restricted_1 === ring KK_0

socleSummands(KK_0)
socleSummands(KK_3)

apply(restricted, i -> socleSummands(image syz i))

-- EXAMPLE CODE FOR PAPER

kk = ZZ/(101);
S = kk[a..e];
I = ideal"a5, b5, c5, d5, e5";
L = orbitRepresentatives(S, I, (3,3,3,3)); #L
B = select(L, l -> isBurch(l)); #B
B_0
KK = killCycleComplexes(S, B_0, 4);
cycleSummands KK_0
cycleSummands KK_3
restricted = restrictTarget(KK_0, KK_3);
netList apply(restricted, i -> betti i)
apply(restricted, i -> socleSummands(image syz i, Verbose => false))
