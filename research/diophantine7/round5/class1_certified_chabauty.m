// Certified elliptic Chabauty for the nontrivial partial-descent class.
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
y0 := (7*b^5 + 24*b^4 - 37*b^3 - 112*b^2 + 83*b - 144)/273;
assert y0^2 eq Evaluate(quartic,K!0);
H := HyperellipticCurve(quartic);
Pbase := H![K!0,y0,K!1];
E,HtoE := EllipticCurve(H,Pbase);

// Two independent points supplied by the initial search.
ok,G,GtoE := PseudoMordellWeilGroup(E);
assert Invariants(G) eq [2,0,0];
free2 := [GtoE(G.2),GtoE(G.3)];
assert IsLinearlyIndependent(free2);

// The unique residual 2-Selmer class has a point already at search bound 10.
covers,maps,abmap := TwoDescent(E : RemoveTorsion:=true,
    RemoveGens:=Seqset(free2), MinRed:=true, WithMaps:=true);
assert #covers eq 1;
residualPts := Points(covers[1] : Bound:=10);
assert #residualPts gt 0;
R3 := maps[1](residualPts[1]);
free3 := free2 cat [R3];
assert IsLinearlyIndependent(free3);
print "CLASS1_RANK_LOWER", #free3;

// The previously certified 2-Selmer computation gives rank <= 3.  Saturating
// at 2 makes the index of the displayed full-rank subgroup odd.
sat3 := Saturation(free3,2 : TorsionFree:=true);
assert #sat3 eq 3 and IsLinearlyIndependent(sat3);
print "CLASS1_SATURATED_AT_2", true;
print "CLASS1_FREE_GENERATORS", sat3;

Tor,TorMap := TorsionSubgroup(E);
assert Invariants(Tor) eq [2];
torPt := TorMap(Tor.1);
A := AbelianGroup([2,0,0,0]);
images := [torPt] cat sat3;
AtoE := map<A->E | x :-> &+[Eltseq(x)[i]*images[i] : i in [1..4]]>;

P1 := ProjectiveSpace(Q,1);
HtoP1 := map<H->P1 | [H.1,H.3]>;
EtoP1 := Expand(Inverse(HtoE)*HtoP1);
SetVerbose("EllChab",2);
V,R := Chabauty(AtoE,EtoP1 : IndexBound:=2,
    SmoothBound:=100, PrimeBound:=50, InitialPrimes:=100);
X := {EtoP1(AtoE(v)) : v in V};
print "CLASS1_CHABAUTY_R", R;
print "CLASS1_RATIONAL_T", X;
assert PrimeDivisors(R) subset {2};
assert X eq {P1![0,1],P1![1,1]};
print "CLASS1_CERTIFIED_CHABAUTY_FINISHED";
