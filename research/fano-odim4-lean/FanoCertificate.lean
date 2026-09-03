import Mathlib

open scoped BigOperators

namespace FanoOdim4

example : (1 : ℚ) + 1 = 2 := by norm_num

/-- Positive weighted sums preserve strict inequality over a nonempty finite index set. -/
theorem positiveWeightedStrict
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight lhs rhs : ι → ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hlt : ∀ i, lhs i < rhs i) :
    (∑ i, weight i * lhs i) < ∑ i, weight i * rhs i := by
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (by
    intro i hi
    exact mul_lt_mul_of_pos_left (hlt i) (hweight i))

/-- Strict Farkas soundness. -/
theorem strictFarkasSemantic
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight lhs rhs : ι → ℝ) (targetLhs targetRhs : ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hlt : ∀ i, lhs i < rhs i)
    (hleft : (∑ i, weight i * lhs i) = targetLhs)
    (hright : (∑ i, weight i * rhs i) ≤ targetRhs) :
    targetLhs < targetRhs := by
  calc
    targetLhs = ∑ i, weight i * lhs i := hleft.symm
    _ < ∑ i, weight i * rhs i := positiveWeightedStrict weight lhs rhs hweight hlt
    _ ≤ targetRhs := hright

/-- Strict Motzkin soundness. -/
theorem strictMotzkinSemantic
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight lhs rhs : ι → ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hlt : ∀ i, lhs i < rhs i)
    (hleft : (∑ i, weight i * lhs i) = 0)
    (hright : (∑ i, weight i * rhs i) < 0) : False := by
  have hsum := positiveWeightedStrict weight lhs rhs hweight hlt
  rw [hleft] at hsum
  exact (not_lt_of_ge (le_of_lt hsum)) hright

#print axioms positiveWeightedStrict
#print axioms strictFarkasSemantic
#print axioms strictMotzkinSemantic

end FanoOdim4
