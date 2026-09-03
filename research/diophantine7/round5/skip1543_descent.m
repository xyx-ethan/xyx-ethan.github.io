// One-factor partial descent omitting the expensive bad prime 1543.
// If the resulting upper set equals the images of known global points, this
// already certifies the exact partial Selmer set.
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
assert #fac eq 2 and 49*fac[1][1]*fac[2][1] eq KT!P;
pts := RationalPoints(P,2 : Bound := 10000);

SetVerbose("CycCov",2);
Sel, alg := qCoverPartialDescent(P,[*g*],2 :
    KnownPoints := pts,
    PrimeBound := 500,
    PrimeCutoff := 2);
print "SKIP1543_SIZE", #Sel;
print "SKIP1543_SET", Sel;
print "SKIP1543_DOMAIN", Domain(alg);
print "SKIP1543_CODOMAIN", Codomain(alg);

knownImages := {};
for p in pts do
    if p[3] ne 0 then
        x0 := Q!p[1];
        Include(~knownImages,alg(Evaluate(g,K!x0)));
    end if;
end for;
print "KNOWN_IMAGE_SIZE", #knownImages;
print "KNOWN_IMAGES", knownImages;
print "UPPER_EQUALS_KNOWN", {alg(K!d[1]):d in Sel} eq knownImages;

i:=0;
for delta in Sel do
    i+:=1;
    d:=K!delta[1];
    quartic:=d*g;
    hits:=[];
    for p in pts do
        if p[3] ne 0 then
            x0:=Q!p[1];
            ok,y0:=IsSquare(Evaluate(quartic,K!x0));
            if ok then Append(~hits,<x0,y0>); end if;
        end if;
    end for;
    print "CLASS",i,delta;
    print "CLASS_REP",i,d;
    print "CLASS_QUARTIC",i,quartic;
    print "CLASS_HITS",i,hits;
end for;
print "SKIP1543_FINISHED";
