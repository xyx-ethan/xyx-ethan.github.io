SetColumns(0);
SetSeed(20260903);
Q:=Rationals(); Qx<x>:=PolynomialRing(Q);
h:=x^2+4*x-4;
H:=x^4-4*x^3-12*x^2+128*x-64;
f:=h*H;
C:=HyperellipticCurve(f);
Hk,AtoHk:=TwoCoverDescent(C : PrimeBound:=1153);
A<th>:=Domain(AtoHk);
reps:=[ hh @@ AtoHk : hh in Hk ];
print "HKSIZE",#Hk;

knownqs:=[Q|0,1,2,-4,-5,18,-66/7];
for q in knownqs do
    print "KNOWN_CLASS",q,AtoHk(q-th);
end for;
print "INFINITY_CLASS",AtoHk(A!1);

Qz<z>:=PolynomialRing(Q);
mp:=z^6-1424*z^4+892928*z^2-303038464;
L<e>:=NumberField(mp);
print "FIELD_DEGREE",Degree(L);
print "FIELD_SIGNATURE",Signature(L);
LX<X>:=PolynomialRing(L);
zeta:=12*(1280-e^2)/(e^2-512);
eta:=-4*(zeta+64)/e;
aa:=(-4+eta)/2;
cc:=(-4-eta)/2;
bb:=(zeta+e)/2;
dd:=(zeta-e)/2;
H1:=X^2+aa*X+bb;
H2:=X^2+cc*X+dd;
print "FACTOR_OK",H1*H2 eq Evaluate(H,X);
print "H1",H1;
print "H2",H2;
g4:=Evaluate(h,X)*H1;
print "G4",g4;
print "G4_FACTOR",Factorization(g4);
LTHETA<THETA>:=quo<LX|g4>;
j:=hom<A->LTHETA|THETA>;
gammas:=[Norm(j(delta)):delta in reps];
for i in [1..#reps] do
    print "REP_GAMMA",i,reps[i],gammas[i];
end for;

classes:=[];
for i in [1..#gammas] do
    isnew:=true;
    for k in classes do
        if IsSquare(gammas[i]/gammas[k]) then isnew:=false; break; end if;
    end for;
    if isnew then Append(~classes,i); end if;
end for;
print "GAMMA_CLASS_INDICES",classes;
print "GAMMA_CLASS_COUNT",#classes;

P1:=ProjectiveSpace(Q,1);
for ci in [1..#classes] do
    i:=classes[ci]; gamma:=gammas[i];
    print "CLASS_BEGIN",ci,"REP_INDEX",i;
    q0:=Q!0; y0:=L!0; found:=false;
    for q in knownqs do
        boo,rt:=IsSquare(gamma*Evaluate(g4,L!q));
        if boo and not found then
            q0:=q; y0:=rt; found:=true;
            print "BASEPOINT_FOUND",q0,y0;
        end if;
    end for;
    if not found then
        boo,rt:=IsSquare(gamma);
        if boo then
            print "BASEPOINT_INFINITY",rt;
        else
            print "NO_BASEPOINT_FROM_KNOWN";
            continue;
        end if;
    end if;
    E:=HyperellipticCurve(gamma*g4);
    if found then
        P0:=E![L!q0,y0,L!1];
    else
        P0:=E![L!1,rt,L!0];
    end if;
    print "POINT_CHECK",P0;
    Eprime,EtoEprime:=EllipticCurve(E,P0);
    print "ELLIPTIC",Eprime;
    EtoP1:=map<E->P1|[E.1,E.3]>;
    EprimeToP1:=Expand(Inverse(EtoEprime)*EtoP1);
    success,MWgrp,MWmap:=PseudoMordellWeilGroup(Eprime);
    print "PMW",success,Invariants(MWgrp);
    if success then
        V,R:=Chabauty(MWmap,EprimeToP1 : IndexBound:=2);
        print "CHABAUTY_R",R;
        images:={ Extend(EprimeToP1)(MWmap(v)) : v in V };
        print "CHABAUTY_IMAGES",images;
    end if;
    print "CLASS_END",ci;
end for;
print "DEGREE6_DONE";
