import FanoLowerBound.RatioCircuitCore

/-!
# Distinctness of two barycentric ratios from four-point general position

If two barycentric ratios coincide, the ratio-circuit identity eliminates the
corresponding two basis points.  The remaining four points then admit two
different affine-coordinate vectors with total weight one, contradicting
affine independence.
-/

namespace FanoLowerBound

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Equality of the first two ratios forces affine dependence of
`r, q, v₂, v₃`.  Hence those four points being affinely independent proves
that the ratios are different. -/
theorem ratio01_ne_of_four_affineIndependent
    (v0 v1 v2 v3 q r : E)
    (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
    (hq : q = a0 • v0 + a1 • v1 + a2 • v2 + a3 • v3)
    (hr : r = b0 • v0 + b1 • v1 + b2 • v2 + b3 • v3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (hb : b0 + b1 + b2 + b3 = 1)
    (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0) (ha3 : a3 ≠ 0)
    (hfour : AffineIndependent ℝ (![r, q, v2, v3] : Fin 4 → E)) :
    b0 / a0 ≠ b1 / a1 := by
  intro hratio
  let t0 : ℝ := b0 / a0
  let t1 : ℝ := b1 / a1
  let t2 : ℝ := b2 / a2
  let t3 : ℝ := b3 / a3
  have hmul0 : a0 * t0 = b0 := by
    dsimp [t0]
    field_simp
  have hmul1 : a1 * t1 = b1 := by
    dsimp [t1]
    field_simp
  have hmul2 : a2 * t2 = b2 := by
    dsimp [t2]
    field_simp
  have hmul3 : a3 * t3 = b3 := by
    dsimp [t3]
    field_simp
  have hr' : r = (a0 * t0) • v0 + (a1 * t1) • v1 +
      (a2 * t2) • v2 + (a3 * t3) • v3 := by
    rw [hmul0, hmul1, hmul2, hmul3]
    exact hr
  have hat : a0 * t0 + a1 * t1 + a2 * t2 + a3 * t3 = 1 := by
    rw [hmul0, hmul1, hmul2, hmul3]
    exact hb
  have ht01 : t0 = t1 := by
    exact hratio
  have hvec := ordered_ratio_vector_identity
    v0 v1 v2 v3 q r a0 a1 a2 a3 t0 t1 t2 t3 hq hr'
  have hscalar := ordered_ratio_scalar_identity
    a0 a1 a2 a3 t0 t1 t2 t3 ha hat
  let f : Fin 4 → E := ![r, q, v2, v3]
  let wL : Fin 4 → ℝ := ![1, 0, 0, 0]
  let wR : Fin 4 → ℝ :=
    ![0, t1, -(a2 * (t1 - t2)), -(a3 * (t1 - t3))]
  have hwL : ∑ i, wL i = 1 := by
    norm_num [wL, Fin.sum_univ_succ]
  have hwR : ∑ i, wR i = 1 := by
    rw [ht01] at hscalar
    simp [wR, Fin.sum_univ_succ]
    linarith
  have hvec' : r - t1 • q + (a2 * (t1 - t2)) • v2 +
      (a3 * (t1 - t3)) • v3 = 0 := by
    rw [ht01] at hvec
    simpa using hvec
  have hbase : r = t1 • q + (-(a2 * (t1 - t2))) • v2 +
      (-(a3 * (t1 - t3))) • v3 := by
    rw [← sub_eq_zero]
    calc
      r - (t1 • q + (-(a2 * (t1 - t2))) • v2 +
          (-(a3 * (t1 - t3))) • v3) =
          r - t1 • q + (a2 * (t1 - t2)) • v2 +
            (a3 * (t1 - t3)) • v3 := by module
      _ = 0 := hvec'
  have hlin : (∑ i, wL i • f i) = ∑ i, wR i • f i := by
    simpa [f, wL, wR, Fin.sum_univ_succ] using hbase
  have hcomb : Finset.univ.affineCombination ℝ f wL =
      Finset.univ.affineCombination ℝ f wR := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hwL]
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hwR]
    exact hlin
  have heq : wL = wR :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ f).1
      hfour wL wR hwL hwR hcomb
  have h0 := congrFun heq 0
  norm_num [wL, wR] at h0

#print axioms ratio01_ne_of_four_affineIndependent

end FanoLowerBound
