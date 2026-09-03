// Single-prime elliptic Chabauty for class 1.  The workflow replaces
// __PTEST__ by the rational prime to test.
Q := Rationals();
Rb<b0> := PolynomialRing(Q);
K<b> := NumberField(b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12);
KT<T> := PolynomialRing(K);
P := 49*T^8 - 100*T^7 + 84*T^6 - 196*T^5 + 278*T^4 - 92*T^3 - 12*T^2 + 4*T + 1;
g := Factorization(P)[1][1];
d := (11*b^5 + 34*b^4 - 99*b^3 - 254*b^2 + 357*b + 420)/39;
y0 := (7*b^5 + 24*b^4 - 37*b^3 - 112*b^2 + 83*b - 144)/273;
H := HyperellipticCurve(d*g);
E,HtoE := EllipticCurve(H,H![K!0,y0,K!1]);

T2 := E![
 (16*b^5+53*b^4-222*b^3-529*b^2+1122*b+696)/39,
 (32*b^5+106*b^4-444*b^3-1058*b^2+2244*b+1392)/39, 1];
P1 := E![0,
 (112*b^5+358*b^4-1580*b^3-3586*b^2+7360*b+6432)/39, 1];
P2 := E![
 (100*b^5+315*b^4-1186*b^3-2965*b^2+5420*b+4896)/39,
 (-1708*b^5-4192*b^4+19688*b^3+35986*b^2-76906*b-64392)/39, 1];
P3 := E![
 (7123*b^5+18477*b^4-109061*b^3-210909*b^2+482303*b+404809)/16848,
 (-1196813*b^5-2333043*b^4+15251611*b^3+21587379*b^2-58665313*b-46460231)/606528, 1];
assert Order(T2) eq 2;
assert IsLinearlyIndependent([P1,P2,P3]);
assert #Saturation([P1,P2,P3],2 : TorsionFree:=true) eq 3;

A := AbelianGroup([2,0,0,0]);
imgs := [T2,P1,P2,P3];
AtoE := map<A->E | z :-> &+[Eltseq(z)[i]*imgs[i] : i in [1..4]]>;
P1line := ProjectiveSpace(Q,1);
HtoP1 := map<H->P1line | [H.1,H.3]>;
EtoP1 := Expand(Inverse(HtoE)*HtoP1);
p := __PTEST__;
SetVerbose("EllChab",1);
N,V,R,L := Chabauty(AtoE,EtoP1,p : Bound:=100);
X := {EtoP1(AtoE(v)) : v in V};
print "PTEST",p;
print "N",N;
print "NV",#V;
print "R",R;
print "X",X;
print "RESIDUAL_COSETS",L;
print "POWER_OF_TWO_R", PrimeDivisors(R) subset {2};
print "COMPLETE_AT_P", N eq #V and PrimeDivisors(R) subset {2};
print "SINGLE_PRIME_FINISHED";
