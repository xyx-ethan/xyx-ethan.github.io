// Rational Diophantine 7-tuple project, round 5.
// Factor the remaining genus-3 exceptional curve as quartic times quartic
// over the degree-six pairing field and perform a first exact partial descent.
SetSeed(20260903);
Q := Rationals();
Rt<t> := PolynomialRing(Q);
P := 49*t^8 - 100*t^7 + 84*t^6 - 196*t^5 + 278*t^4 - 92*t^3 - 12*t^2 + 4*t + 1;

Rv<v0> := PolynomialRing(Q);
Fv := v0^6 - 8676*v0^4 + 24361088*v0^2 - 23386973184;
print "PAIRING_FIELD_POLY", Fv;
print "PAIRING_FIELD_IRREDUCIBLE", IsIrreducible(Fv);
K<v> := NumberField(Fv);
print "PAIRING_FIELD_SIGNATURE", Signature(K);
print "PAIRING_FIELD_DISC", Discriminant(Integers(K));
print "PAIRING_FIELD_CLASS_NUMBER", ClassNumber(K);

KT<T> := PolynomialRing(K);
p := (v-50)/49;
r := (-v-50)/49;
r0 := (v^3 - 50*v^2 - 3088*v - 152928)/(4802*v);
s0 := (v^3 + 50*v^2 - 3088*v + 152928)/(4802*v);
q1 := T^2 + p*T + r0;
q2 := T^2 + r*T + s0;
q := 49*T^4 - 100*T^3 - 12*T^2 + 128*T - 64;
assert 49*q1*q2 eq q;

g1 := (T^2+1)^2 + p*(T^2+1)*(T+1) + r0*(T+1)^2;
g2 := (T^2+1)^2 + r*(T^2+1)*(T+1) + s0*(T+1)^2;
assert 49*g1*g2 eq Evaluate(P,T);
print "Q1", q1;
print "Q2", q2;
print "G1", g1;
print "G2", g2;
print "P_FACTOR_CHECK", 49*g1*g2 eq Evaluate(P,T);
print "P_FACTOR_OVER_K", Factorization(Evaluate(P,T));

pts := RationalPoints(P,2 : Bound := 10000);
print "KNOWN_P_POINTS", pts;
SetVerbose("CycCov",1);
try
    Sel, alg := qCoverPartialDescent(P,[*g1,49*g2*],2 : KnownPoints := pts, PrimeBound := 100);
    print "PARTIAL_SIZE", #Sel;
    print "PARTIAL_SET", Sel;
    print "PARTIAL_DOMAIN", Domain(alg);
    print "PARTIAL_CODOMAIN", Codomain(alg);
    i := 0;
    for delta in Sel do
        i +:= 1;
        print "PARTIAL_CLASS", i, delta;
        print "PARTIAL_CLASS_FIRST", i, delta[1];
        H := HyperellipticCurve((K!delta[1])*g1);
        print "PARTIAL_CLASS_CURVE", i, H;
        hits := [];
        for x0 in [Q|-1,0,1,1/2,1/3] do
            ok,y0 := IsSquare(Evaluate((K!delta[1])*g1,K!x0));
            if ok then Append(~hits,<x0,y0>); end if;
        end for;
        print "PARTIAL_CLASS_HITS",i,hits;
    end for;
catch err
    print "PARTIAL_ERROR", err;
end try;
print "PAIRING_RECON_FINISHED";
