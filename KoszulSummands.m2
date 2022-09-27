-- -*- coding: utf-8 -*-

newPackage(
	"KoszulSummands",
	Version => "0.1",
	Date => "October, 2022",
	AuxiliaryFiles => false,
	Authors => {{Name => "Daniel Rostamloo", Email => "drostamloo@berkeley.edu"},
	    {Name => "David Eisenbud", Email => "de@math.berkeley.edu"}},
	Headline => "Determining Socle Summands Property in Koszul resolutions of Artin Local Rings",
	PackageExports => {"Points", "DGAlgebras", "MonomialOrbits"},
	DebuggingMode => true)
    
export{
    "koszulIdeals", "socle", "socleSummands", "hasSocleSummand", "koszulSS"
    }

-- return a list of ideals given by the matrices of the koszul complex of a 
koszulIdeals = method()
koszulIdeals(Ring) := (R) -> (
    KR := koszulComplexDGA R;
    complex := toComplex KR;
    matrices := apply(length complex, i -> complex.dd_(i+1));
    apply(matrices, ker)
    )

socle = method()
socle Module := M -> (
    R := ring M;
    ker (M ** transpose vars R)
    )

socleSummands = method()
socleSummands Module := M ->(
    mm := ideal gens ring M;
    ss := socle M;
    compress (gens ss % (mm*M))
    )

hasSocleSummand = method()
hasSocleSummand Module := M -> (
    0 != socleSummands M)

koszulSS = method()
koszulSS(Ring) := (R) -> (
    K := koszulIdeals(R);
    L := for i in toList(0..length K - 1) list if hasSocleSummand(K_i) then i else continue
    
    )

beginDocumentation()

end--

restart
uninstallPackage "KoszulSummands"
loadPackage ( "KoszulSummands", Reload => true)
S = ZZ/(101)[x,y,z]
I = ideal (x^5, y^5, z^5)
R= S/I

koszulSS(R)
