// Rational Diophantine 7-tuple project, round 5.
// Inspect all rational 2-power isogeny targets of the complementary genus-2
// quotient and test whether its rank-three Jacobian becomes elliptically split.
SetSeed(20260903);
Q := Rationals();
R<u> := PolynomialRing(Q);
f := (u^2 + 4*u - 4)*(49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64);
C := HyperellipticCurve(f);
J := Jacobian(C);

print "ISOGENY_START";
print "CONDUCTOR", Conductor(C);
print "ABS_INVARIANTS", AbsoluteInvariants(C);
print "RICHELOT", RichelotIsogenousSurfaces(J);
print "DOUBLE_RICHELOT", DoubleRichelotIsogenies(J);
Js, products, restrictions := TwoPowerIsogenies(J);
print "N_JACOBIANS", #Js;
print "N_PRODUCTS", #products;
print "N_RESTRICTIONS", #restrictions;
for i in [1..#Js] do
    A := Js[i];
    print "JACOBIAN", i, A;
    print "JACOBIAN_RANK_BOUNDS", i, RankBounds(A);
    print "JACOBIAN_TWO_SELMER", i, Invariants(TwoSelmerGroup(A));
end for;
for i in [1..#products] do
    A := products[i];
    print "PRODUCT", i, A;
    print "PRODUCT_FACTOR1_RANK", RankBounds(A[1]);
    print "PRODUCT_FACTOR2_RANK", RankBounds(A[2]);
end for;
for i in [1..#restrictions] do
    E := restrictions[i];
    print "RESTRICTION", i, E;
    print "RESTRICTION_FIELD", BaseField(E);
    try
        print "RESTRICTION_RANK", i, RankBounds(E);
    catch err
        print "RESTRICTION_RANK_ERROR", i, err;
    end try;
end for;
print "ISOGENY_FINISHED";
