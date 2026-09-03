// Elliptic Chabauty for the unit class in the exact partial Selmer set.
SetSeed(20260903);
Q := Rationals();
Rt<t> := PolynomialRing(Q);
P := 49*t^8 - 100*t^7 + 84*t^6 - 196*t^5 + 278*t^4 - 92*t^3 - 12*t^2 + 4*t + 1;
Rb<b0> := PolynomialRing(Q);
Fb := b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12;
K<b> := NumberField(Fb);
KT<T> := PolynomialRing(K);
fac := Factorization(KT!P);
g := fac[1][1];
assert #fac eq 2 and fac[1][2] eq 1 and fac[2][2] eq 1;
assert 49*g*fac[2][1] eq KT!P;

H := HyperellipticCurve(g);
assert Evaluate(g,K!-1) eq 4;
Pbase := H![K!-1,K!2,K!1];
E,HtoE := EllipticCurve(H,Pbase);
print "CLASS0_FIELD", K;
print "CLASS0_QUARTIC", g;
print "CLASS0_ELLIPTIC", E;

knownT := [Q|-1,0,1,1/2,1/3];
knownHits := [];
for x0 in knownT do
    ok,y0 := IsSquare(Evaluate(g,K!x0));
    if ok then Append(~knownHits,<x0,y0>); end if;
end for;
print "CLASS0_KNOWN_HITS", knownHits;
print "CLASS0_INFINITY", PointsAtInfinity(H);

SetVerbose("MordellWeil",1);
ok,G,GtoE := PseudoMordellWeilGroup(E);
print "CLASS0_PMW_SUCCESS", ok;
print "CLASS0_MW_GROUP", G;
print "CLASS0_MW_INVARIANTS", Invariants(G);
print "CLASS0_MW_IMAGES", [GtoE(G.i):i in [1..Ngens(G)]];
assert ok;
P1 := ProjectiveSpace(Q,1);
HtoP1 := map<H->P1 | [H.1,H.3]>;
EtoP1 := Expand(Inverse(HtoE)*HtoP1);
SetVerbose("EllChab",2);
V,R := Chabauty(GtoE,EtoP1 : IndexBound := 2, SmoothBound := 100, PrimeBound := 50, InitialPrimes := 100);
X := {EtoP1(GtoE(v)):v in V};
print "CLASS0_CHABAUTY_V", V;
print "CLASS0_CHABAUTY_R", R;
print "CLASS0_RATIONAL_T", X;
print "CLASS0_FINISHED";
