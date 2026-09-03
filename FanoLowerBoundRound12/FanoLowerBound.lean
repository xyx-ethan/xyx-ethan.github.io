import FanoLowerBound.RatioCircuitCore
import FanoLowerBound.RadonNormalization
import FanoLowerBound.AffineBasisReduction
import FanoLowerBound.DirectFivePointRadon
import FanoLowerBound.RatioDistinctness
import FanoLowerBound.SixthCoordinates
import FanoLowerBound.SixPointRatioPairs
import FanoLowerBound.AllPositiveSixPointRadon

/-!
# Fano lower-bound Round 15

This kernel target certifies the arithmetic-to-geometry Radon bridge, the
affine-basis reduction from six-point general position in `ℝ³`, direct strict
Radon witnesses for the two-positive and three-positive barycentric sign
patterns, nonvanishing coordinates for both extra points, all six pairwise
barycentric-ratio inequalities, and the sorted all-positive six-point branch.
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
#print axioms FanoLowerBound.sixPoint_ratio02_ne
#print axioms FanoLowerBound.sixPoint_ratio03_ne
#print axioms FanoLowerBound.sixPoint_ratio12_ne
#print axioms FanoLowerBound.sixPoint_ratio13_ne
#print axioms FanoLowerBound.sixPoint_ratio23_ne
#print axioms FanoLowerBound.sixPointRatio_injective
#print axioms FanoLowerBound.allPositive_sixPoint_strictRadon23
