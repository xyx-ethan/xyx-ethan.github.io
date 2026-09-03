// Test whether the known rational-t fibres already contain a rank-three
// Mordell--Weil subgroup on either elliptic cover.
SetSeed(20260903);
Q := Rationals();
Rb<b0> := PolynomialRing(Q);
Fb := b0^6 + 3*b0^5 - 11*b0^4 - 27*b0^3 + 41*b0^2 + 55*b0 + 12;
K<b> := NumberField(Fb);
KT<T> := PolynomialRing(K);
P := 49*T^8 - 100*T^7 + 84*T^6 - 196*T^5 + 278*T^4 - 92*T^3 - 12*T^2 + 4*T + 1;
g := Factorization(P)[1][1];

procedure GreedyRank(label, E, images)
    free := [];
    for R in images do
        if R ne E!0 then
            if #free eq 0 or IsLinearlyIndependent(free cat [R]) then
                Append(~free,R);
                print label,"ADD",#free,R;
                if #free eq 3 then break; end if;
            end if;
        end if;
    end for;
    print label,"RANK_LOWER",#free;
    print label,"FREE",free;
end procedure;

// Unit class.
H0 := HyperellipticCurve(g);
B0 := H0![K!-1,K!2,K!1];
E0,m0 := EllipticCurve(H0,B0);
y12 := (K!1/1092)*(-24*b^5-34*b^4+424*b^3+540*b^2-1748*b-1161);
y13 := (K!1/2457)*(-48*b^5-68*b^4+848*b^3+1080*b^2-3496*b-2322);
HP0 := [
    H0![K!-1,K!2,K!1], H0![K!-1,K!-2,K!1],
    H0![K!1/2,y12,K!1], H0![K!1/2,-y12,K!1],
    H0![K!1/3,y13,K!1], H0![K!1/3,-y13,K!1]
] cat Setseq(PointsAtInfinity(H0));
EP0 := [m0(R):R in HP0];
print "CLASS0_N_KNOWN",#EP0;
GreedyRank("CLASS0",E0,EP0);

// Nontrivial class.
d := (11*b^5 + 34*b^4 - 99*b^3 - 254*b^2 + 357*b + 420)/39;
quartic := d*g;
y0 := (7*b^5 + 24*b^4 - 37*b^3 - 112*b^2 + 83*b - 144)/273;
assert y0^2 eq Evaluate(quartic,K!0);
assert (2*y0)^2 eq Evaluate(quartic,K!1);
H1 := HyperellipticCurve(quartic);
B1 := H1![K!0,y0,K!1];
E1,m1 := EllipticCurve(H1,B1);
HP1 := [
    H1![K!0,y0,K!1], H1![K!0,-y0,K!1],
    H1![K!1,2*y0,K!1], H1![K!1,-2*y0,K!1]
] cat Setseq(PointsAtInfinity(H1));
EP1 := [m1(R):R in HP1];
print "CLASS1_N_KNOWN",#EP1;
GreedyRank("CLASS1",E1,EP1);
print "KNOWN_POINT_RANK_FINISHED";
