// Rational Diophantine 7-tuple project, round 5.
// Determine parity and attempt to determine the exact Mordell-Weil rank of
// the complementary genus-2 quotient.
SetSeed(20260903);
Q := Rationals();
R<u> := PolynomialRing(Q);
f := (u^2 + 4*u - 4)*(49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64);
C := HyperellipticCurve(f);
J := Jacobian(C);

print "MW_RANK_START";
print "HAS_SQUARE_SHA", HasSquareSha(J);
print "RANK_BOUNDS_INITIAL", RankBounds(J);
SetVerbose("MordellWeilGroup", 2);
G, m, finite, proved, ub := MordellWeilGroupGenus2(J :
    RankOnly := true,
    BoundC := 50000,
    SearchBounds := [5,10,20,50,100,300,1000,3000,10000],
    SearchBounds2 := [100,200,500,1000,3000,10000],
    SearchBounds3 := [10,20,50,100,200,500,1000],
    MaxBound := 10000,
    MaxIndex := 1000,
    TwistSearchBound := 500,
    TwistBound := 500);
print "MW_GROUP", G;
print "MW_INVARIANTS", Invariants(G);
print "MW_FINITE_INDEX", finite;
print "MW_PROVED", proved;
print "MW_RANK_UPPER", ub;
print "MW_IMAGES", [m(G.i): i in [1..Ngens(G)]];
print "MW_RANK_FINISHED";
