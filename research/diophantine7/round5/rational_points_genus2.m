// Rational Diophantine 7-tuple project, round 5.
// Attempt a complete rational-point classification on the complementary
// genus-2 quotient using Michael Stoll's RationalPointsGenus2 intrinsic.
SetSeed(20260903);
Q := Rationals();
R<u> := PolynomialRing(Q);
h := u^2 + 4*u - 4;
q := 49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64;
f := h*q;
C := HyperellipticCurve(f);

print "RPG2_START";
print "CURVE", C;
print "AUT_Q", AutomorphismGroup(C);
print "GEOM_AUT_QBAR", GeometricAutomorphismGroup(C);
pts, complete, bound := RationalPointsGenus2(C :
    Bound1 := 10000,
    Bound2 := 50000,
    Fast := true,
    RankBound := 3,
    PrimeCutoff := 10000);
print "RPG2_COMPLETE", complete;
print "RPG2_BOUND", bound;
print "RPG2_COUNT", #pts;
print "RPG2_POINTS", pts;

known := RationalPoints(f,2 : Bound := 10000);
print "KNOWN_COUNT", #known;
print "KNOWN_SUBSET", known subset pts;
if complete then
    assert known eq pts;
end if;
print "RPG2_FINISHED";
