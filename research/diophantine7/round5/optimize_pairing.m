// Optimize the degree-six pairing field used in round 5.
Q := Rationals();
R<v> := PolynomialRing(Q);
F := v^6 - 8676*v^4 + 24361088*v^2 - 23386973184;
K<a> := NumberField(F);
L<b>, mp := OptimizedRepresentation(K);
print "OPT_FIELD", L;
print "OPT_POLY", DefiningPolynomial(L);
print "IMAGE_OLD_GENERATOR", mp(a);
print "PREIMAGE_NEW_GENERATOR", b@@mp;
print "OPT_DISC", Discriminant(Integers(L));
print "OPT_SIGNATURE", Signature(L);
print "OPT_CLASS_NUMBER", ClassNumber(L);
print "OPT_UNITS", UnitGroup(Integers(L));
print "OPT_FINISHED";
