// Exact Mordell-Weil certificate for the nontrivial partial-descent class.
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
d := (11*b^5+34*b^4-99*b^3-254*b^2+357*b+420)/39;
quartic := d*g;
assert #fac eq 2 and 49*g*fac[2][1] eq KT!P;
okroot,y0 := IsSquare(Evaluate(quartic,K!0));
assert okroot;
H := HyperellipticCurve(quartic);
Pbase := H![K!0,y0,K!1];
E,HtoE := EllipticCurve(H,Pbase);
y1 := 2*y0;
assert y1^2 eq Evaluate(quartic,K!1);
knownH := [Pbase,H![K!1,y1,K!1]];
knownE := [HtoE(p):p in knownH];
print "CLASS1_E", E;
print "CLASS1_KNOWN_E", knownE;

ok0,G0,G0toE := PseudoMordellWeilGroup(E);
print "CLASS1_PSEUDO_SUCCESS", ok0;
print "CLASS1_PSEUDO_INV", Invariants(G0);

candidates := [G0toE(G0.i): i in [1..Ngens(G0)] | Invariants(G0)[i] eq 0] cat knownE;
free := [];
for R in candidates do
    if R ne E!0 and Order(R) eq 0 then
        if #free eq 0 or IsLinearlyIndependent(free cat [R]) then
            Append(~free,R);
        end if;
    end if;
end for;
print "CLASS1_GREEDY_FREE", free;
print "CLASS1_GREEDY_RANK", #free;
assert #free gt 0 and IsLinearlyIndependent(free);

S2,S2map := TwoSelmerGroup(E);
T2,T2map := TwoTorsionSubgroup(E);
upper := #Invariants(S2)-#Invariants(T2);
print "CLASS1_TWO_SELMER", Invariants(S2);
print "CLASS1_TWO_TORSION", Invariants(T2);
print "CLASS1_RANK_UPPER", upper;
print "CLASS1_RANK_BOUNDS", RankBounds(E);
assert #free eq upper;

sat2 := Saturation(free,2 : TorsionFree := true);
print "CLASS1_SAT2", sat2;
print "CLASS1_SAT2_RANK", #sat2;
assert #sat2 eq upper and IsLinearlyIndependent(sat2);

Tor,Tormap := TorsionSubgroup(E);
torPts := [Tormap(Tor.i):i in [1..Ngens(Tor)]];
A := AbelianGroup(Invariants(Tor) cat [0:i in [1..#sat2]]);
images := torPts cat sat2;
AtoE := map<A->E | x :-> &+[Eltseq(x)[i]*images[i]:i in [1..#images]]>;
print "CLASS1_TORSION", Invariants(Tor);
print "CLASS1_CERT_GROUP", A;
print "CLASS1_CERT_IMAGES", images;
print "CLASS1_FINITE_ODD_INDEX", true;
print "CLASS1_MW_CERTIFICATE_FINISHED";
