// Search the unique residual 2-cover for a third independent point, class 1.
SetSeed(20260903);
Q := Rationals();
Rb<b0> := PolynomialRing(Q);
Fb := b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12;
K<b> := NumberField(Fb);
KT<T> := PolynomialRing(K);
P := 49*T^8 - 100*T^7 + 84*T^6 - 196*T^5 + 278*T^4 - 92*T^3 - 12*T^2 + 4*T + 1;
fac := Factorization(P); g := fac[1][1];
d := (11*b^5 + 34*b^4 - 99*b^3 - 254*b^2 + 357*b + 420)/39;
quartic := d*g;
okroot,y0 := IsSquare(Evaluate(quartic,K!0)); assert okroot;
H := HyperellipticCurve(quartic);
Pbase := H![K!0,y0,K!1];
E,HtoE := EllipticCurve(H,Pbase);
ok,G,GtoE := PseudoMordellWeilGroup(E);
assert Invariants(G) eq [2,0,0];
free := [GtoE(G.2),GtoE(G.3)];
assert IsLinearlyIndependent(free);

covers,maps,abmap := TwoDescent(E : RemoveTorsion:=true,
    RemoveGens:=Seqset(free), MinRed:=true, WithMaps:=true);
assert #covers eq 1;
print "CLASS1_REDUCED_MODEL", Eltseq(GenusOneModel(covers[1]));
for B in [10,30,100,300,1000,3000,10000,30000] do
    pts := Points(covers[1] : Bound:=B);
    print "CLASS1_SEARCH",B,#pts;
    if #pts gt 0 then
        images := [maps[1](p): p in pts];
        print "CLASS1_POINTS", pts;
        print "CLASS1_IMAGES", images;
        for R in images do
            print "CLASS1_RANK3", IsLinearlyIndependent(free cat [R]);
        end for;
        break;
    end if;
end for;
print "CLASS1_RESIDUAL_SEARCH_FINISHED";
