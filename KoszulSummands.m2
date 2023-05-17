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
    "complexSocSummands", -- given an arbitrary chain complex, return a list of which cycles have socle summands
    "subrows", -- like the method submatrix, but for choosing a subset of rows instead of columns
    "original", -- given a chain complex K2 and another chain complex K1 which is its summand in the first coordinate, return the boundary maps of K2 with the source restricted to the columns of K1
    "project",
    "previous",
    "ignore",
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

subrows = method()
subrows(Matrix, List) := (M, rows) -> (
    transpose submatrix(transpose M, rows)
)

original = method()
original(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    orig := apply(length K2, i -> submatrix(d2_i, toList(0 .. numcols d1_i - 1)))
)

project = method()
project(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    onTarget := apply(length K2, i -> subrows(d2_i, toList(0 .. numrows d1_i - 1)));
    
    onSource := apply(length onTarget, i -> submatrix(onTarget_i, toList(numcols d1_i .. numcols d2_i - 1)))

)

previous = method()
previous(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    onTarget := apply(length K2, i -> subrows(d2_i, toList(0 .. numrows d1_i - 1)))
)

ignore = method()
ignore(ChainComplex, ChainComplex) := (K1, K2) -> (
    d1 := K1.dd;
    d2 := K2.dd;
    
    onTarget := apply(length K2, i -> subrows(d2_i, toList(numrows d1_i .. numrows d2_i - 1)));
    
    onSource := apply(length onTarget, i -> submatrix(onTarget_i, toList(numcols d1_i .. numcols d2_i - 1)))

)

cycleSummands = method(Options => {Verbose => false})
cycleSummands(ChainComplex) := o -> K -> (
    c := length K;
    cycles := for i from 0 to c list image syz K.dd_i;
    for i from 0 to c list socleSummands(cycles_i, o)
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
		    	S = ZZ/101[a,b,c,d]
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
		    	S = ZZ/101[a,b,c,d]
			f = matrix{{a,b,c,d}}
			K = koszul(f)
			complexSocSummands(K)
		      
///

doc ///
        Key 
	        subrows
	        (subrows, Matrix, List)
	Headline
	    	Forms the submatrix given by a subset of the rows of a given matrix.
	Usage
	        subrows(M, rows)
	Inputs
	    	M:Matrix
		rows:List
	Outputs
	    	:Matrix
		    	Row-wise submatrix of M
	Description
	    	Text
		    	Given M a matrix and rows a list of indices corresponding to the rows of M, form the row-wise submatrix of M given by those rows.
		Example
			f = matrix{{1,2,3},{4,5,6},{7,8,9}}
			subrows(f, {1,2})
///

doc ///
	Key 
	        original
	        (original, ChainComplex, ChainComplex)
	Headline
	    	Restricts the source of the boundary maps of a chain complex to a summand of the chain complex.
	Usage
	        original(K1, K2)
	Inputs
	    	K1:ChainComplex
		    	A summand of the chain complex K2
		K2:ChainComplex
		    	A chain complex
	Outputs
	    	:List
		    	List of restricted boundary maps
	Description
	    	Text
		    	Given a chain complex and a summand of it, return a list consisting of the boundary maps with their source restricted to the summand
		Example
		    	S = ZZ/101[a,b,c,d]
			f = matrix{{a, b, c, d}}
			K1 = koszul(f)
			K2 = K1 ++ K1
			original(K1, K2)
		      
///

doc ///
	Key 
	    	project
	        (project, ChainComplex, ChainComplex)
	Headline
	    	Projects the image of the boundary maps of a chain complex onto a summand of the chain complex.
	Usage
	        project(K1, K2)
	Inputs
	    	K1:ChainComplex
		    	A summand of the chain complex K2
		K2:ChainComplex
		    	A chain complex
	Outputs
	    	:List
		    	List of restricted boundary maps
	Description
	    	Text
		    	Given a chain complex and a summand of it, return a list consisting of the boundary maps with their target restricted to the summand
		Example
		    	S = ZZ/101[a,b,c,d]
	                f = matrix{{a, b, c, d}}
			K1 = koszul(f)
			K2 = K1 ++ K1
			project(K1, K2)
		      
///

doc ///
	Key 
	        ignore
	        (ignore, ChainComplex, ChainComplex)
	Headline
	        Return a list of boundary maps which ignores a given summand of the chain complex with respect to both the source and the target.
	Usage
	        ignore(K1, K2)
	Inputs
	    	K1:ChainComplex
		    	A summand of the chain complex K2
		K2:ChainComplex
		    	A chain complex
	Outputs
	    	:List
		    	List of restricted boundary maps
	Description
	    	Text
		    	Given a chain complex and a summand of it, return a list consisting of the boundary maps where the source and target do not involve the summand.
		Example
		    	S = ZZ/101[a,b,c,d]
	                f = matrix{{a, b, c, d}}
			K1 = koszul(f)
			K2 = K1 ++ K1
		        ignore(K1, K2)
		      
///

doc ///
	Key 
	        cycleSummands
	        (cycleSummands, ChainComplex)
	Headline
	        Given a chain complex, determine the socle summand property for the cycles of the chain complex.
	Usage
	        cycleSummands(K)
	Inputs
	    	K:ChainComplex
		    	A chain complex
	Outputs
	    	:List
		        A list indicating the number of socle summands occuring in each homological degree starting from 1, and optionally the degree of the socle summands.
	Description
	    	Text
		    	Given a chain complex, extract the matrices giving the cycles and use socleSummands to check for socle summands in each homological degree.
		Example
		        S = ZZ/101[a,b,c,d]
		        f = matrix{{a,b,c,d}}
		        K = koszul(f)
		        cycleSummands(K)
		      
///

end--
///
restart
uninstallPackage "KoszulSummands"
restart
installPackage "KoszulSummands"
viewHelp KoszulSummands
///
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
-*
------------------------------------------------------------------------------------
DEAR DAVID: START HERE
------------------------------------------------------------------------------------
*-

-- Choosing ideals for tests. We will end up choosing a Burch ideal because they are nice to test on.
kk = ZZ/(101);
S = kk[a..d];
I = ideal"a5, b5, c5, d5";
L = orbitRepresentatives(S, I, (3,3,3,3)); #L
B = select(L, l -> isBurch(l)); #B
NB = select(L, l -> not isBurch(l)); #NB
NG = select(L, b -> not isGolod(S/b)); #NG
NBNG = select(NB, l -> not isGolod(S/l)); #NBNG
tally for l in B list depth(l, S)

-- Making the Koszul complex for the maximal ideal and building the resolution of the residue class field by killing cycles step by step in increasing homological degree
KK = killCycleComplexes(S, B_1, 2);

-- Check the socle summands in the cycles for the original Koszul complex and after one step of killing cycles. We will use these below to try understanding what is going on.
cycleSummands KK_0
cycleSummands KK_1

-- project() gives the projection of the boundary maps (excluding maps in the original Koszul complex) to the original Koszul complex at every homological degree
proj = project(KK_0, KK_1);

-- orig() selects the boundary maps of the original Koszul complex from KK_1
orig = original(KK_0, KK_1);

-- ignore() selects the boundary maps which have neither source nor target involving the original Koszul complex.
ig = ignore(KK_0, KK_1);

-- previous() is like project(), but it also selects maps in the original Koszul complex.
prev = previous(KK_0, KK_1);

-- Naively quotient the cycles of the original Koszul complex by the projection of the new boundary maps and check socle summands; surprisingly (to me), none of the socle summands of the original Koszul complex in any homological degree survive after this.
apply(length KK_1 - 1, i -> socleSummands(image (syz(orig_i) % proj_(i+1)) , Verbose => false))

-- Check for socle elements that are not in the  product of the maximal ideal and the image of the projections of the previous boundary maps. Note the use of previous() here instead of project(). Numerologically, I don't immediately see a pattern from this output when comparing to the outputs of cycleSummands from above.
mm = ideal gens ring KK_0;
apply(length KK_1 - 1, i ->  flatten degrees source (gens socle image syz orig_i % (mm*image prev_(i+1))))

-- These were numerologically interesting to me. The socle summands upstairs were killed, but the socle summands in the cycles of the projected boundary maps as well as the boundary maps having nothing to do with the original Koszul complex seem to remember the socle summands they killed. Note the additive relations, especially comparing the first instance where the number of socle summands changed between KK_0 and KK_1.
apply(length KK_1, i -> socleSummands(image syz proj_(i)))
apply(length KK_1, i -> socleSummands(image syz ig_(i)))


loadedPackages
kk = ZZ/(101);
S = kk[a..d];
B = ideal"a5,a2b,ab2,b5,abc,c5,abd,d5"
KK = killCycleComplexes(S, B, 2);
cycleSummands KK_0
cycleSummands KK_1
proj = project(KK_0, KK_1);
prev = previous(KK_0, KK_1);
orig = original(KK_0, KK_1);
ig = ignore(KK_0, KK_1);
mm = ideal gens ring KK_0;
apply(length KK_1 - 1, i ->  numcols compress (gens (socle image syz orig_i) % (mm*image prev_(i+1))))
apply(length KK_1 - 1, i -> socleSummands(image (syz(orig_i) % proj_(i+1))))
apply(length KK_1, i -> socleSummands(image syz proj_(i)))
apply(length KK_1, i -> socleSummands(image syz ig_(i)))
