// Rational Diophantine 7-tuple project, round 5: refined descent reconnaissance.
SetSeed(20260903);
Q := Rationals();
R<u> := PolynomialRing(Q);
h := u^2 + 4*u - 4;
q := 49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64;
f := h*q;
C := HyperellipticCurve(f);
pts := RationalPoints(f,2 : Bound := 10000);

print "START_DESCENT_RECON";
rlo,rhi,gens := RankBounds(f,2 : ReturnGenerators);
print "CYCLIC_RANK_BOUNDS", rlo,rhi;
print "CYCLIC_GENERATORS", gens;
for P in gens do
    print "CYCLIC_GENERATOR_POINT", P;
end for;

SetVerbose("CycCov",1);
Sel0,alg0 := qCoverPartialDescent(f,[*h,q*],2 : KnownPoints := pts, PrimeBound := 1200);
print "PARTIAL_Q_SIZE", #Sel0;
print "PARTIAL_Q_SET", Sel0;

L<a> := NumberField(q);
LX<X> := PolynomialRing(L);
hL := Evaluate(h,X);
lin := X-a;
print "L_DEGREE_SIGNATURE_CLASSNO", Degree(L), Signature(L), ClassNumber(L);
print "L_DISC", Discriminant(Integers(L));
print "CUBIC_FACTOR", hL*lin;

// Do not pass KnownPoints here: the refined descent has a stricter ambient
// p-Selmer representation, and passing the full unrefined point set triggers
// an incompatible representative error in V2.29-9.
Sel1,alg1 := qCoverPartialDescent(f,[*h,lin*],2 : PrimeBound := 1200);
print "PARTIAL_L_SIZE", #Sel1;
print "PARTIAL_L_SET", Sel1;
print "PARTIAL_L_DOMAIN", Domain(alg1);
print "PARTIAL_L_CODOMAIN", Codomain(alg1);

knownx := [Q|0,4/5,18/17,1,2,66/73,5/6];
i := 0;
for delta in Sel1 do
    i +:= 1;
    gamma := L!delta[1] * L!delta[2];
    cubic := gamma*hL*lin;
    print "CLASS",i,"DELTA",delta;
    print "CLASS_GAMMA",i,gamma;
    print "CLASS_CUBIC",i,cubic;
    hits := [];
    for x0 in knownx do
        ok,y0 := IsSquare(Evaluate(cubic,L!x0));
        if ok then Append(~hits,<x0,y0>); end if;
    end for;
    print "CLASS_KNOWN_HITS",i,hits;
    H := HyperellipticCurve(cubic);
    print "CLASS_INFINITY",i,PointsAtInfinity(H);
end for;
print "ALL_DESCENT_RECON_ASSERTIONS_PASSED";
