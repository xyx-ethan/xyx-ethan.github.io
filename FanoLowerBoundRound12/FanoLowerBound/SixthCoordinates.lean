import FanoLowerBound.AffineBasisReduction

/-!
# Nonzero barycentric coordinates of the sixth point

The same replacement argument used for the fifth point applies to index `5`.
These nonvanishing coordinates imply that every barycentric ratio βᵢ/αᵢ is
nonzero once the fifth-point coordinates αᵢ are also known to be nonzero.
-/

namespace FanoLowerBound

/-- Replace the first basis index by index `5`. -/
def replaceSixthEmb0 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 1, 2, 3]
  inj' := by decide

/-- Replace the second basis index by index `5`. -/
def replaceSixthEmb1 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 5, 2, 3]
  inj' := by decide

/-- Replace the third basis index by index `5`. -/
def replaceSixthEmb2 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 1, 5, 3]
  inj' := by decide

/-- Replace the fourth basis index by index `5`. -/
def replaceSixthEmb3 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 1, 2, 5]
  inj' := by decide

/-- The sixth point can replace any one of the first four points without losing
 affine independence. -/
theorem replacePoint_sixth_affineIndependent
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    AffineIndependent ℝ (replacePoint (firstFourAffineBasis p hgp) (p 5) i) := by
  fin_cases i
  · have hfun : replacePoint (firstFourAffineBasis p hgp) (p 5) 0 =
        p ∘ replaceSixthEmb0 := by
      funext j
      fin_cases j <;> rfl
    change AffineIndependent ℝ
      (replacePoint (firstFourAffineBasis p hgp) (p 5) (0 : Fin 4))
    rw [hfun]
    exact hgp replaceSixthEmb0
  · have hfun : replacePoint (firstFourAffineBasis p hgp) (p 5) 1 =
        p ∘ replaceSixthEmb1 := by
      funext j
      fin_cases j <;> rfl
    change AffineIndependent ℝ
      (replacePoint (firstFourAffineBasis p hgp) (p 5) (1 : Fin 4))
    rw [hfun]
    exact hgp replaceSixthEmb1
  · have hfun : replacePoint (firstFourAffineBasis p hgp) (p 5) 2 =
        p ∘ replaceSixthEmb2 := by
      funext j
      fin_cases j <;> rfl
    change AffineIndependent ℝ
      (replacePoint (firstFourAffineBasis p hgp) (p 5) (2 : Fin 4))
    rw [hfun]
    exact hgp replaceSixthEmb2
  · have hfun : replacePoint (firstFourAffineBasis p hgp) (p 5) 3 =
        p ∘ replaceSixthEmb3 := by
      funext j
      fin_cases j <;> rfl
    change AffineIndependent ℝ
      (replacePoint (firstFourAffineBasis p hgp) (p 5) (3 : Fin 4))
    rw [hfun]
    exact hgp replaceSixthEmb3

/-- Every barycentric coordinate of the sixth point with respect to the first
four is nonzero. -/
theorem sixth_coord_ne_zero
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    (firstFourAffineBasis p hgp).coord i (p 5) ≠ 0 :=
  coord_ne_zero_of_replacePoint_affineIndependent
    (firstFourAffineBasis p hgp) (p 5) i
    (replacePoint_sixth_affineIndependent p hgp i)

/-- The four sixth-point coordinates sum to one. -/
theorem sixth_coord_sum_eq_one
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    ∑ i, (firstFourAffineBasis p hgp).coord i (p 5) = 1 := by
  simpa using (firstFourAffineBasis p hgp).sum_coord_apply_eq_one (p 5)

/-- Every ratio of a sixth-point coordinate by the corresponding fifth-point
coordinate is nonzero. -/
theorem sixth_over_fifth_coord_ne_zero
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    (firstFourAffineBasis p hgp).coord i (p 5) /
      (firstFourAffineBasis p hgp).coord i (p 4) ≠ 0 := by
  exact div_ne_zero (sixth_coord_ne_zero p hgp i) (fifth_coord_ne_zero p hgp i)

#print axioms sixth_coord_ne_zero
#print axioms sixth_over_fifth_coord_ne_zero

end FanoLowerBound
