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
    "koszulIdeals", "koszulSS"
    }

-- return a list of ideals given by the matrices of the koszul complex of a 
koszulIdeals = method()
koszulIdeals(Ring) := (R) -> (
    KR := koszulComplexDGA R;
    complex := toComplex KR;
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
    
    alg := apply(n, i -> ((dgAlgebraMultMap(K,A_1))_i*socSummands_i)%(vars R **cyc_i))
    
    bool := apply(n, i -> alg_i == 0)
    
    dom1 := ring 
    )


beginDocumentation()

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
L = orbitRepresentatives(S, I, monomialIdeal J, -6); #L

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
needsPackage "DGAlgebras"
S = ZZ/101[a,b]
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
cyc = apply(n, i-> syz K.dd_(i+1))
socSummands = apply(n, i-> soc_i%(vars R**cyc_i))
target socSummands_0 == K_1

cyc_0*(soc_0//cyc_0)
soc_0%(vars R ** cyc_0)
-- what is the purpose of this?

(dgAlgebraMultMap(K,A_1))_1*socSummands_0
inj0 = ((dgAlgebraMultMap(K,A_1))_1*socSummands_0)%(vars R **cyc_1)

inj0 = ((dgAlgebraMultMap(K,A_0))_1*socSummands_0)%(vars R **cyc_1)
inj1 = ((dgAlgebraMultMap(K,A_1))_1*socSummands_0)%(vars R **cyc_1)
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



viewHelp dgAlgebraMultMap
