import FanoLowerBound.RadonNormalization

/-!
# Direct strict Radon witnesses from barycentric sign patterns

If the barycentric coordinates of a fifth point relative to four affine-basis
vertices already have two or three positive entries, the five points themselves
have a strict `2--3` Radon partition. These two canonical lemmas are the
normalization primitives used after permuting the four basis vertices.
-/

namespace FanoLowerBound

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Canonical `2+2` barycentric sign pattern: `a₀,a₁>0` and `a₂,a₃<0`. -/
theorem two_positive_direct_strictRadon23
    (v0 v1 v2 v3 q : E) (a0 a1 a2 a3 : ℝ)
    (hq : q = a0 • v0 + a1 • v1 + a2 • v2 + a3 • v3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : a2 < 0) (ha3 : a3 < 0) :
    StrictRadon23 v0 v1 q v2 v3 := by
  let S : ℝ := a0 + a1
  have hS : 0 < S := by dsimp [S]; linarith
  have hSne : S ≠ 0 := ne_of_gt hS
  have hsum : 1 + (-a2) + (-a3) = S := by
    dsimp [S]
    linarith
  have hcomb : a0 • v0 + a1 • v1 =
      (1 : ℝ) • q + (-a2) • v2 + (-a3) • v3 := by
    rw [hq]
    module
  refine ⟨a0 / S, a1 / S, 1 / S, (-a2) / S, (-a3) / S,
    div_pos ha0 hS, div_pos ha1 hS, div_pos zero_lt_one hS,
    div_pos (neg_pos.mpr ha2) hS, div_pos (neg_pos.mpr ha3) hS, ?_, ?_, ?_⟩
  · rw [← add_div, show a0 + a1 = S by rfl, div_self hSne]
  · rw [← add_div, ← add_div, hsum, div_self hSne]
  · have hs := congrArg (fun z : E => (1 / S) • z) hcomb
    simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hs

/-- Canonical `3+1` barycentric sign pattern: `a₀,a₁,a₂>0` and `a₃<0`. -/
theorem three_positive_direct_strictRadon23
    (v0 v1 v2 v3 q : E) (a0 a1 a2 a3 : ℝ)
    (hq : q = a0 • v0 + a1 • v1 + a2 • v2 + a3 • v3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : a3 < 0) :
    StrictRadon23 q v3 v0 v1 v2 := by
  let S : ℝ := a0 + a1 + a2
  have hS : 0 < S := by dsimp [S]; linarith
  have hSne : S ≠ 0 := ne_of_gt hS
  have hsum : 1 + (-a3) = S := by
    dsimp [S]
    linarith
  have hcomb : (1 : ℝ) • q + (-a3) • v3 =
      a0 • v0 + a1 • v1 + a2 • v2 := by
    rw [hq]
    module
  refine ⟨1 / S, (-a3) / S, a0 / S, a1 / S, a2 / S,
    div_pos zero_lt_one hS, div_pos (neg_pos.mpr ha3) hS,
    div_pos ha0 hS, div_pos ha1 hS, div_pos ha2 hS, ?_, ?_, ?_⟩
  · rw [← add_div, hsum, div_self hSne]
  · rw [← add_div, ← add_div, show a0 + a1 + a2 = S by rfl, div_self hSne]
  · have hs := congrArg (fun z : E => (1 / S) • z) hcomb
    simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hs

#print axioms two_positive_direct_strictRadon23
#print axioms three_positive_direct_strictRadon23

end FanoLowerBound
