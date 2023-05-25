getVariableChunks = method()
getVariableChunks DGAlgebra := A -> (
   ns := values (tally (gens A.natural) / degree / first);
   partSumNs := {0} | apply(#ns, i -> sum take(ns, i+1));
   varsA := apply(#ns, i -> (gens A.natural)_(toList(partSumNs#i..partSumNs#(i+1)-1)));
   varsA
)

chunkDegree = method()
chunkDegree (RingElement,List) := (f,L) -> (sum apply(L, l -> degree(l,f)))*(first degree first L)

getPhiMap = method()
getPhiMap (DGAlgebra, List, List) := (A, inVec, outVec) -> (
   if (sum inVec != sum outVec + 1) then return null;
   varsA := getVariableChunks A;
   h := #varsA;
   if h != #inVec or h != #outVec then return null;
   inBasis := tensor apply(h, i -> basis(inVec#i,A.natural,Variables => varsA#i));
   outBasis := tensor apply(h, i -> basis(outVec#i,A.natural,Variables => varsA#i));
   diffs := matrix {apply(flatten entries inBasis, m -> diff(A,m))};
   last coefficients(diffs, Monomials => outBasis)
)

degreeVecs = method()
degreeVecs (DGAlgebra,ZZ) := (A,d) -> (
   varsA := getVariableChunks A;
   basisA := flatten entries basis(d,A.natural);
   sort unique apply(basisA, m -> apply(varsA, l -> chunkDegree(m,l)))
)

displayBlockDiff = method()
displayBlockDiff (DGAlgebra, ZZ) := (A,d) -> (
   inputDegs := degreeVecs(A,d);
   outputDegs := degreeVecs(A,d-1);
   firstRow := {{}} | inputDegs;
   myNet := {firstRow} | apply(outputDegs, o -> {o} | apply(inputDegs, i -> getPhiMap(A,i,o)));
   netList myNet
)

blockDiff = method()
blockDiff (DGAlgebra, ZZ) := (A,d) -> (
   inputDegs := degreeVecs(A,d);
   outputDegs := degreeVecs(A,d-1);
   matrix table(#outputDegs, #inputDegs, (a,b) -> getPhiMap(A,inputDegs#b,outputDegs#a))
)

end

restart
debug needsPackage "DGAlgebras"
load "blockDiff.m2"

R = QQ[x,y,z]/(ideal(x^3,y^3,z^3))
A = acyclicClosure(R)

-- another example
R = QQ[x,y,z]/(ideal(x^3,y^3,z^3,x*y*z))
A = acyclicClosure(R,EndDegree => 2)
displayBlockDiff(A,5)
X = blockDiff(A,4)
--none of the following work:
X^[0,2,3]_[1,0,3]
X^[1,0,3]_[0,2,3]
X^[{1,0,3}]_[{0,2,3}]


-- this displays the differential with headings corresponding to the (i,j) and (p,q)
displayBlockDiff(A,3)


-- this creates the matrix as a "matrix of matrices"

-- which one may then select blocks using X^[...]_[...]
X^[0]
X^[0]_[0]
-- this is the differential returned by DGAlgebras by default
polyDifferential(7,A)
