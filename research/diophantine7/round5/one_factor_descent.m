// Correct one-factor partial descent for the remaining size-4 genus-3 orbit.
SetSeed(20260903);
Q := Rationals();
Rt<t> := PolynomialRing(Q);
P := 49*t^8 - 100*t^7 + 84*t^6 - 196*t^5 + 278*t^4 - 92*t^3 - 12*t^2 + 4*t + 1;
assert IsIrreducible(P);

Rb<b0> := PolynomialRing(Q);
Fb := b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12;
K<b> := NumberField(Fb);
KT<T> := PolynomialRing(K);
fac := Factorization(KT!P);
print "OPT_FACTORISATION", fac;
assert #fac eq 2;
assert &and[e[1] eq 1 : e in fac];
g := fac[1][1];
gbar := fac[2][1];
assert 49*g*gbar eq KT!P;
print "SELECTED_FACTOR", g;
print "CONJUGATE_FACTOR", gbar;

pts := RationalPoints(P,2 : Bound := 10000);
print "KNOWN_POINTS", pts;
SetVerbose("CycCov",2);
Sel, alg := qCoverPartialDescent(P,[*g*],2 :
    KnownPoints := pts,
    PrimeBound := 200,
    PrimeCutoff := 2000);
print "PARTIAL_SIZE", #Sel;
print "PARTIAL_SET", Sel;
print "PARTIAL_DOMAIN", Domain(alg);
print "PARTIAL_CODOMAIN", Codomain(alg);
print "KNOWN_IMAGE_SIZE", #{alg(<Evaluate(g,K!p[1]),>): p in pts | p[3] ne 0};

i := 0;
for delta in Sel do
    i +:= 1;
    d := K!delta[1];
    quartic := d*g;
    hits := [];
    for p in pts do
        if p[3] ne 0 then
            x0 := Q!p[1];
            ok,y0 := IsSquare(Evaluate(quartic,K!x0));
            if ok then Append(~hits,<x0,y0>); end if;
        end if;
    end for;
    print "CLASS", i, delta;
    print "CLASS_REP", i, d;
    print "CLASS_QUARTIC", i, quartic;
    print "CLASS_KNOWN_HITS", i, hits;
    H := HyperellipticCurve(quartic);
    print "CLASS_INFINITY", i, PointsAtInfinity(H);
end for;
print "ONE_FACTOR_DESCENT_FINISHED";
