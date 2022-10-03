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

beginDocumentation()

end--

restart
uninstallPackage "KoszulSummands"
loadPackage ( "KoszulSummands", Reload => true)
loadPackage ( "MonomialOrbits", Reload => true)
S = ZZ/(101)[x,y,z,w]
I = ideal (x^3, y^3, z^3, w^3)
J = compress (gens ((ideal vars S)^4) % I);
R= S/I

koszulSS(R)

L = orbitRepresentatives(S, I,monomialIdeal J, -3); #L

elapsedTime tally for i in G list koszulSS(S/i)
elapsedTime tally for i in G list kSS(S/i, 6)

select(L, l -> koszulSS(S/l)_0 == 0)

koszulSS(S/trim(L_1))
trim(L_1)

-- Conjecture 1: Every burch ring has socle summands in every koszul cycle after 2

select(L, l -> isGolod(S/l))

