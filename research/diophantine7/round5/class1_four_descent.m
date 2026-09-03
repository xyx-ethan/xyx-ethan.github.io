// Determine whether the sole residual 2-Selmer class for cover class 1
// lifts to an everywhere locally soluble 4-cover.
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
covers,maps,abmap := TwoDescent(E : RemoveTorsion:=true,
    RemoveGens:=Seqset(free), MinRed:=false, WithMaps:=true);
assert #covers eq 1;
print "CLASS1_RESIDUAL_COUNT", #covers;
SetVerbose("FourDescent",2);
four := FourDescent(covers[1] : MinRed:=false);
print "CLASS1_FOUR_COVER_COUNT", #four;
print "CLASS1_FOUR_DESCENT_FINISHED";
