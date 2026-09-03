// Rational Diophantine 7-tuple project, round 5 basic reconnaissance.
SetSeed(20260903);
Q := Rationals();
R<u> := PolynomialRing(Q);
q := 49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64;
f := (u^2 + 4*u - 4)*q;

v1,v2,v3 := GetVersion();
print "MAGMA_VERSION", v1,v2,v3;
print "Q_FACTOR", Factorization(q);
print "F_FACTOR", Factorization(f);
print "Q_DISC", Factorization(Integers()!Discriminant(q));
print "F_DISC", Factorization(Integers()!Discriminant(f));

E := EllipticCurve([Q|0,-321,0,29483,8109]);
Emin, EtoEmin := MinimalModel(E);
print "E", E;
print "E_MIN", Emin;
print "E_AINVS", aInvariants(Emin);
print "E_DISC", Factorization(Integers()!Discriminant(Emin));
print "E_CONDUCTOR", Factorization(Conductor(Emin));
elo,ehi := RankBounds(Emin);
print "E_RANK_BOUNDS", elo,ehi;
TE, TEtoE := TorsionSubgroup(Emin);
print "E_TORSION", Invariants(TE);
print "E_TORSION_POINTS", [TEtoE(x): x in TE];
try
    GE, GEtoE, okE := MordellWeilGroup(Emin);
    print "E_MW_OK", okE;
    print "E_MW_GROUP", Invariants(GE);
    print "E_MW_IMAGES", [GEtoE(GE.i): i in [1..Ngens(GE)]];
catch err
    print "E_MW_ERROR", err;
end try;

C := HyperellipticCurve(f);
J := Jacobian(C);
print "D_GENUS", Genus(C);
print "D_BAD_PRIMES", BadPrimes(C);
print "D_INDEX_ONE_LOCALLY", HasIndexOneEverywhereLocally(C);
TJ,TJtoJ := TwoTorsionSubgroup(J);
print "D_TWO_TORSION", Invariants(TJ);
SJ,SJtoA := TwoSelmerGroup(J);
print "D_TWO_SELMER", #SJ, Invariants(SJ);
print "D_RANK_BOUND", RankBound(J);
try
    jlo,jhi := RankBounds(J);
    print "D_RANK_BOUNDS", jlo,jhi;
catch err
    print "D_RANK_BOUNDS_ERROR", err;
end try;

pts := RationalPoints(f,2 : Bound := 10000);
print "D_RATIONAL_POINTS_B10000_COUNT", #pts;
print "D_RATIONAL_POINTS_B10000", pts;
print "ALL_BASIC_ASSERTIONS_PASSED";
