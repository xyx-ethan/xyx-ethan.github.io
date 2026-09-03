SetColumns(0);
SetSeed(20260903);
Q:=Rationals(); Qx<x>:=PolynomialRing(Q);
h:=x^2+4*x-4;
H:=x^4-4*x^3-12*x^2+128*x-64;
f:=h*H;
C:=HyperellipticCurve(f);
Hk,AtoHk:=TwoCoverDescent(C : PrimeBound:=1153);
A<th>:=Domain(AtoHk);
print "HKSIZE",#Hk;
knownqs:=[Q|0,1,2,-4,-5,18,-66/7];
knownclasses:={ AtoHk(q-th) : q in knownqs } join { AtoHk(A!1) };
print "KNOWN_CLASS_COUNT",#knownclasses;
print "ALL_CLASSES_REPRESENTED",knownclasses eq Hk;
for q in knownqs do
    print "KNOWN_CLASS",q,AtoHk(q-th),"DELTA",Evaluate(h,q),"DELTA_SQUARE",IsSquare(Evaluate(h,q));
end for;
print "INFINITY_CLASS",AtoHk(A!1);

// A paired-root quadratic factor H1 of the irreducible quartic H.
Qz<z>:=PolynomialRing(Q);
mp:=z^6-1424*z^4+892928*z^2-303038464;
L<e>:=NumberField(mp);
LX<X>:=PolynomialRing(L);
zeta:=12*(1280-e^2)/(e^2-512);
eta:=-4*(zeta+64)/e;
aa:=(-4+eta)/2;
cc:=(-4-eta)/2;
bb:=(zeta+e)/2;
dd:=(zeta-e)/2;
H1:=X^2+aa*X+bb;
H2:=X^2+cc*X+dd;
assert H1*H2 eq Evaluate(H,X);
print "FIELD_DEGREE",Degree(L),"SIGNATURE",Signature(L);
print "H1",H1;

// Parametrize h(q)=square by q=(t^2+1)/(t+1).
LT<t>:=PolynomialRing(L);
G0:=(t^2+1)^2 + aa*(t^2+1)*(t+1) + bb*(t+1)^2;
d1:=Evaluate(H1,L!1);
G1:=G0/d1;
print "G0",G0;
print "D1",d1;
print "G1",G1;
assert Degree(G0) eq 4 and Degree(G1) eq 4;
assert IsSquare(Evaluate(G0,L!-1));
assert IsSquare(Evaluate(G1,L!0));

P1:=ProjectiveSpace(Q,1);
curves:=[* <G0,L!-1>, <G1,L!0> *];
for i in [1..#curves] do
    G:=curves[i][1]; t0:=curves[i][2];
    boo,y0:=IsSquare(Evaluate(G,t0)); assert boo;
    CQ:=HyperellipticCurve(G);
    P0:=CQ![t0,y0,L!1];
    print "CURVE_BEGIN",i;
    print "BASEPOINT",P0;
    EQ,mpEQ:=EllipticCurve(CQ,P0);
    print "ELLIPTIC",EQ;
    CQtoP1:=map<CQ->P1|[CQ.1,CQ.3]>;
    EQtoP1:=Expand(Inverse(mpEQ)*CQtoP1);
    success,MWgrp,MWmap:=PseudoMordellWeilGroup(EQ);
    print "PMW_SUCCESS",success;
    print "PMW_INVARIANTS",Invariants(MWgrp);
    print "PMW_IMAGES",[MWmap(MWgrp.i):i in [1..Ngens(MWgrp)]];
    if success then
        V,R:=Chabauty(MWmap,EQtoP1 : IndexBound:=2);
        images:={ Extend(EQtoP1)(MWmap(v)) : v in V };
        print "CHABAUTY_R",R;
        print "CHABAUTY_IMAGES",images;
    end if;
    print "CURVE_END",i;
end for;
print "TWO_QUARTICS_DONE";
