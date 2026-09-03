import FanoLowerBound.RatioCircuitCore
import FanoLowerBound.RadonNormalization
import FanoLowerBound.AffineBasisReduction
import FanoLowerBound.DirectFivePointRadon
import FanoLowerBound.RatioDistinctness
import FanoLowerBound.SixthCoordinates
import FanoLowerBound.SixPointRatioPairs

/-!
# Fano lower-bound Round 14

This kernel target certifies the arithmetic-to-geometry Radon bridge, the
affine-basis reduction from six-point general position in `ℝ³`, the direct
strict Radon witnesses for the two-positive and three-positive barycentric
sign patterns, nonvanishing coordinates for both extra points, the generic
ratio-collision lemma, and its first six-point general-position instance.
-/

#print axioms FanoLowerBound.ordered_ratio_circuit_core
#print axioms FanoLowerBound.ordered_ratio_circuit_strictRadon23
#print axioms FanoLowerBound.firstFourAffineBasis
#print axioms FanoLowerBound.fifth_coord_ne_zero
#print axioms FanoLowerBound.sixth_coord_ne_zero
#print axioms FanoLowerBound.sixth_over_fifth_coord_ne_zero
#print axioms FanoLowerBound.two_positive_direct_strictRadon23
#print axioms FanoLowerBound.three_positive_direct_strictRadon23
#print axioms FanoLowerBound.ratio01_ne_of_four_affineIndependent
#print axioms FanoLowerBound.sixPoint_ratio01_ne
