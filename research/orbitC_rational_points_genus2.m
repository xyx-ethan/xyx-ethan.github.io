SetColumns(0);
SetSeed(20260903);
Q:=Rationals(); Qx<x>:=PolynomialRing(Q);
f:=x^6-32*x^4+96*x^3+496*x^2-768*x+256;
C:=HyperellipticCurve(f);
print "CURVE",C;
pts,proved,bound:=RationalPointsGenus2(
    C : Bound1:=10000, Bound2:=100000, Fast:=false,
        RankBound:=3, PrimeCutoff:=10000);
print "RPG2_POINTS",pts;
print "RPG2_PROVED",proved;
print "RPG2_BOUND",bound;
print "RPG2_DONE";
