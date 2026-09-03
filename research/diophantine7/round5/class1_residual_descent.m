// Residual 2-descent for the nontrivial partial-descent elliptic curve.
SetSeed(20260903);
Q := Rationals();
Rb<b0> := PolynomialRing(Q);
Fb := b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12;
K<b> := NumberField(Fb);
KT<T> := PolynomialRing(K);
P := 49*T^8 - 100*T^7 + 84*T^6 - 196*T^5 + 278*T^4 - 92*T^3 - 12*T^2 + 4*T + 1;
fac := Factorization(P);
g := fac[1][1];
d := (11*b^5 + 34*b^4 - 99*b^3 - 254*b^2 + 357*b + 420)/39;
quartic := d*g;
okroot,y0 := IsSquare(Evaluate(quartic,K!0));
assert okroot;
H := HyperellipticCurve(quartic);
Pbase := H![K!0,y0,K!1];
E,HtoE := EllipticCurve(H,Pbase);

ok,G,GtoE := PseudoMordellWeilGroup(E);
assert Invariants(G) eq [2,0,0];
free := [GtoE(G.2),GtoE(G.3)];
assert IsLinearlyIndependent(free);
print "CLASS1_FREE", free;

SetVerbose("TwoDescent",1);
covers,maps,abmap := TwoDescent(E :
    RemoveTorsion := true,
    RemoveGens := Seqset(free),
    MinRed := false,
    WithMaps := true);
print "CLASS1_RESIDUAL_COUNT", #covers;
print "CLASS1_RESIDUAL_GROUP", Domain(abmap);
for i in [1..#covers] do
    print "CLASS1_RESIDUAL_CURVE",i,covers[i];
    print "CLASS1_RESIDUAL_MAP",i,maps[i];
    pts := Points(covers[i] : Bound := 10000);
    print "CLASS1_RESIDUAL_POINTS_B10000",i,pts;
    if #pts gt 0 then
        images := [maps[i](p):p in pts];
        print "CLASS1_RESIDUAL_IMAGES",i,images;
    end if;
end for;
print "CLASS1_RESIDUAL_FINISHED";
