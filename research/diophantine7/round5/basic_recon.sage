from sage.all import *

proof.all(True)
R.<u> = PolynomialRing(QQ)
q = 49*u^4 - 100*u^3 - 12*u^2 + 128*u - 64
f = (u^2 + 4*u - 4)*q

print("SAGE_VERSION", version())
print("Q_FACTOR", q.factor())
print("F_FACTOR", f.factor())
print("Q_DISC", q.discriminant().factor())
print("F_DISC", f.discriminant().factor())

# Exact Weierstrass model derived from the quartic quotient.
E = EllipticCurve(QQ, [0, -321, 0, 29483, 8109])
Emin = E.global_minimal_model()
print("E_MODEL", E)
print("E_MINIMAL", Emin)
print("E_DISCRIMINANT", E.discriminant().factor())
print("E_CONDUCTOR", E.conductor().factor())
print("E_TORSION", E.torsion_subgroup())
print("E_TORSION_POINTS", E.torsion_points())
print("E_RANK", E.rank(proof=True))
print("E_GENS", E.gens(proof=True))
print("E_REGULATOR", E.regulator_of_points(E.gens(proof=True)))

known_E = [E(139,768), E(27,-768), E(47,888), E(QQ(115)/9, QQ(15616)/27)]
for i,P in enumerate(known_E):
    print("KNOWN_E", i, P, "HEIGHT", P.height())

C = HyperellipticCurve(f)
print("D_GENUS", C.genus())
print("D_BAD_PRIME_CANDIDATES", sorted(set([2] + [p for p,e in ZZ(f.discriminant()).factor()])))
try:
    print("D_RATIONAL_POINTS_B10000", C.rational_points(bound=10000))
except Exception as exc:
    print("D_RATIONAL_POINTS_ERROR", type(exc).__name__, str(exc))

# Finite-field data for independent Jacobian checks.
for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139]:
    if f.discriminant() % p == 0:
        continue
    Cp = HyperellipticCurve(f.change_ring(GF(p)))
    N1 = Cp.count_points(1)
    N2 = Cp.count_points(2)
    a1 = p + 1 - N1
    a2 = (N2 - p^2 - 1 + a1^2)//2
    Jorder = 1 + a1 + a2 + a1*p + p^2
    print("FROB", p, N1, N2, a1, a2, Jorder, factor(Jorder))
