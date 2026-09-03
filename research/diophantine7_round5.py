#!/usr/bin/env sage -python
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

from sage.all import EllipticCurve, HyperellipticCurve, PolynomialRing, QQ

R = PolynomialRing(QQ, "x")
x = R.gen()
H = x**4 - 4*x**3 - 12*x**2 + 128*x - 64
F = x**6 - 32*x**4 + 96*x**3 + 496*x**2 - 768*x + 256

print("=== SAGE VERSION ===", flush=True)
subprocess.run(["sage", "--version"], check=False)

print("=== QUARTIC INVARIANTS / JACOBIAN ===", flush=True)
a, b, c, d, e = 1, -4, -12, 128, -64
I = 12*a*e - 3*b*d + c*c
J = 72*a*c*e + 9*b*c*d - 27*a*d*d - 27*b*b*e - 2*c*c*c
print("I", I, "J", J, flush=True)
E0 = EllipticCurve(QQ, [0, 0, 0, -27*I, -27*J])
E = EllipticCurve(QQ, [0, 0, 0, -1539, 126846])
print("E0", E0, flush=True)
print("E", E, flush=True)
print("E_MIN", E.minimal_model(), flush=True)
print("E_CONDUCTOR", E.conductor(), flush=True)
print("E_TORSION", E.torsion_subgroup(), flush=True)
try:
    print("E_RANK_PROOF", E.rank(proof=True), flush=True)
except Exception as exc:
    print("E_RANK_PROOF_ERROR", type(exc).__name__, str(exc), flush=True)
try:
    print("E_GENS_PROOF", E.gens(proof=True), flush=True)
except Exception as exc:
    print("E_GENS_PROOF_ERROR", type(exc).__name__, str(exc), flush=True)
try:
    Cq = HyperellipticCurve(H)
    print("QUARTIC_CURVE", Cq, "GENUS", Cq.genus(), flush=True)
    print("QUARTIC_JACOBIAN", Cq.jacobian(), flush=True)
except Exception as exc:
    print("QUARTIC_JACOBIAN_ERROR", type(exc).__name__, str(exc), flush=True)

print("=== CLONE G2DESCENT ===", flush=True)
repo = "/tmp/g2descent"
subprocess.run(["rm", "-rf", repo], check=True)
subprocess.run(["git", "clone", "--depth", "1", "https://github.com/sirk390/g2descent.git", repo], check=True)
sys.path.insert(0, repo)
os.chdir(repo)
from descent import rank_bounds_full, rank_bounds_multi  # noqa: E402
coeffs = [256, -768, 496, 96, -32, 0, 1]
print("G2_COEFFS", coeffs, flush=True)
for proof in (False, True):
    try:
        lo, hi, info = rank_bounds_full(coeffs, proof=proof)
        print("G2_RANK_BOUNDS proof=", proof, lo, hi, flush=True)
        print("G2_INFO proof=", proof, json.dumps(info, default=str, sort_keys=True), flush=True)
    except Exception as exc:
        print("G2_DESCENT_ERROR proof=", proof, type(exc).__name__, str(exc), flush=True)
try:
    lo, hi, info = rank_bounds_multi(coeffs)
    print("G2_MULTI", lo, hi, json.dumps(info, default=str, sort_keys=True), flush=True)
except Exception as exc:
    print("G2_MULTI_ERROR", type(exc).__name__, str(exc), flush=True)


def magma_eval(code: str, label: str) -> None:
    data = urllib.parse.urlencode({"input": code}).encode("ascii")
    request = urllib.request.Request(
        "https://magma.maths.usyd.edu.au/xml/calculator.xml",
        data=data,
        headers={
            "Content-Type": "application/x-www-form-urlencoded",
            "Accept": "text/html, application/xml, application/xhtml+xml",
            "Referer": "https://magma.maths.usyd.edu.au/calc/",
            "User-Agent": "Mozilla/5.0 exact-research-check",
        },
        method="POST",
    )
    for attempt in range(8):
        try:
            with urllib.request.urlopen(request, timeout=90) as response:
                raw = response.read().decode("utf-8", "replace")
            root = ET.fromstring(raw)
            offline = root.find("offline")
            if offline is not None:
                print(label, "OFFLINE", offline.text, flush=True)
                time.sleep(15 + 5*attempt)
                continue
            lines = [node.text or "" for node in root.findall("./results/line")]
            print("===", label, "RAW_XML_BEGIN ===", flush=True)
            print(raw, flush=True)
            print("===", label, "LINES_BEGIN ===", flush=True)
            print("\n".join(lines), flush=True)
            print("===", label, "END ===", flush=True)
            return
        except Exception as exc:
            print(label, "ATTEMPT", attempt + 1, "ERROR", type(exc).__name__, str(exc), flush=True)
            time.sleep(15 + 5*attempt)
    print(label, "FAILED_ALL_ATTEMPTS", flush=True)

magma_ell = r'''
SetColumns(0);
Q:=Rationals(); Qx<x>:=PolynomialRing(Q);
H:=x^4-4*x^3-12*x^2+128*x-64;
CQ:=HyperellipticCurve(H); P:=CQ![4,16,1];
EQ,mp:=EllipticCurve(CQ,P);
print "QUARTIC",CQ;
print "ELL_MODEL",EQ;
print "ELL_MIN",MinimalModel(EQ);
print "ELL_COND",Conductor(EQ);
print "ELL_TORS",Invariants(TorsionSubgroup(EQ));
print "ELL_RANKBOUNDS",RankBounds(EQ);
print "ELL_GENERATORS",Generators(EQ);
'''
magma_g2 = r'''
SetColumns(0);
Q:=Rationals(); Qx<x>:=PolynomialRing(Q);
f:=x^6-32*x^4+96*x^3+496*x^2-768*x+256;
C:=HyperellipticCurve(f); J:=Jacobian(C);
print "CURVE",C;
print "BAD",BadPrimes(C);
print "INDEX_ONE",HasIndexOneEverywhereLocally(C);
T,mT:=TwoTorsionSubgroup(J); print "TWO_TORS",#T,Invariants(T);
S,mS:=TwoSelmerGroup(J); print "TWO_SELMER",#S,Invariants(S);
print "RANKBOUND",RankBound(J);
print "RANKBOUNDS",RankBounds(J);
pts:=Points(C : Bound:=10000); print "POINTS",pts;
'''
magma_eval(magma_ell, "MAGMA_ELL")
magma_eval(magma_g2, "MAGMA_G2")
print("=== DONE ===", flush=True)
