import Mathlib

/-!
# Arithmetic core of the 3--2 Radon lemma in dimension three

This file isolates the algebraic identity used in the barycentric-ratio proof.
It deliberately does not yet package the identity into Mathlib's `RadonPartition`
notion.  The file contains only completed declarations and no proof placeholders.
-/

namespace FanoLowerBound

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/--
Let `q = Σ aᵢ vᵢ` and `r = Σ aᵢ tᵢ vᵢ`.  Omitting the second
ratio `t₁`, the following five-point linear relation is identically zero.
The coefficient of `v₁` is written explicitly as `a₁ * (t₁ - t₁)` so that
the omitted point is visible in the statement.
-/
theorem ordered_ratio_vector_identity
    (v0 v1 v2 v3 q r : E)
    (a0 a1 a2 a3 t0 t1 t2 t3 : ℝ)
    (hq : q = a0 • v0 + a1 • v1 + a2 • v2 + a3 • v3)
    (hr : r = (a0 * t0) • v0 + (a1 * t1) • v1 +
        (a2 * t2) • v2 + (a3 * t3) • v3) :
    r - t1 • q
        + (a0 * (t1 - t0)) • v0
        + (a1 * (t1 - t1)) • v1
        + (a2 * (t1 - t2)) • v2
        + (a3 * (t1 - t3)) • v3 = 0 := by
  rw [hq, hr]
  module

/-- The coefficients in `ordered_ratio_vector_identity` sum to zero. -/
theorem ordered_ratio_scalar_identity
    (a0 a1 a2 a3 t0 t1 t2 t3 : ℝ)
    (ha : a0 + a1 + a2 + a3 = 1)
    (hat : a0 * t0 + a1 * t1 + a2 * t2 + a3 * t3 = 1) :
    1 - t1
        + a0 * (t1 - t0)
        + a1 * (t1 - t1)
        + a2 * (t1 - t2)
        + a3 * (t1 - t3) = 0 := by
  calc
    1 - t1
          + a0 * (t1 - t0)
          + a1 * (t1 - t1)
          + a2 * (t1 - t2)
          + a3 * (t1 - t3) =
        (1 - (a0 * t0 + a1 * t1 + a2 * t2 + a3 * t3))
          + t1 * ((a0 + a1 + a2 + a3) - 1) := by ring
    _ = 0 := by rw [ha, hat]; ring

/--
If `t₀ < t₁ < t₂ < t₃`, all `aᵢ` used below are positive, and `t₁ ≠ 0`,
then the nonzero coefficients in the ratio circuit split as `2+3`.

The first disjunct is the case `0 < t₁`: positive coefficients are those
of `v₀` and `r`; negative coefficients are those of `v₂`, `v₃`, and `q`.
The second disjunct is the case `t₁ < 0`: the coefficient of `q` changes
sign, giving three positive and two negative coefficients.
-/
theorem ordered_ratio_sign_pattern
    (a0 a2 a3 t0 t1 t2 t3 : ℝ)
    (ha0 : 0 < a0) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (h01 : t0 < t1) (h12 : t1 < t2) (h23 : t2 < t3)
    (ht1 : t1 ≠ 0) :
    ((0 < a0 * (t1 - t0) ∧ 0 < (1 : ℝ) ∧
        a2 * (t1 - t2) < 0 ∧ a3 * (t1 - t3) < 0 ∧ -t1 < 0) ∨
      (0 < a0 * (t1 - t0) ∧ 0 < (1 : ℝ) ∧ 0 < -t1 ∧
        a2 * (t1 - t2) < 0 ∧ a3 * (t1 - t3) < 0)) := by
  have hb0 : 0 < a0 * (t1 - t0) := mul_pos ha0 (sub_pos.mpr h01)
  have hb2 : a2 * (t1 - t2) < 0 :=
    mul_neg_of_pos_of_neg ha2 (sub_neg.mpr h12)
  have h13 : t1 < t3 := h12.trans h23
  have hb3 : a3 * (t1 - t3) < 0 :=
    mul_neg_of_pos_of_neg ha3 (sub_neg.mpr h13)
  rcases lt_or_gt_of_ne ht1 with ht1neg | ht1pos
  · exact Or.inr ⟨hb0, zero_lt_one, neg_pos.mpr ht1neg, hb2, hb3⟩
  · exact Or.inl ⟨hb0, zero_lt_one, hb2, hb3, neg_neg_of_pos ht1pos⟩

/-- Combined arithmetic/vector-space core of the ordered ratio circuit. -/
theorem ordered_ratio_circuit_core
    (v0 v1 v2 v3 q r : E)
    (a0 a1 a2 a3 t0 t1 t2 t3 : ℝ)
    (hq : q = a0 • v0 + a1 • v1 + a2 • v2 + a3 • v3)
    (hr : r = (a0 * t0) • v0 + (a1 * t1) • v1 +
        (a2 * t2) • v2 + (a3 * t3) • v3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (hat : a0 * t0 + a1 * t1 + a2 * t2 + a3 * t3 = 1)
    (ha0 : 0 < a0) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (h01 : t0 < t1) (h12 : t1 < t2) (h23 : t2 < t3)
    (ht1 : t1 ≠ 0) :
    (r - t1 • q
          + (a0 * (t1 - t0)) • v0
          + (a1 * (t1 - t1)) • v1
          + (a2 * (t1 - t2)) • v2
          + (a3 * (t1 - t3)) • v3 = 0) ∧
      (1 - t1
          + a0 * (t1 - t0)
          + a1 * (t1 - t1)
          + a2 * (t1 - t2)
          + a3 * (t1 - t3) = 0) ∧
      (((0 < a0 * (t1 - t0) ∧ 0 < (1 : ℝ) ∧
          a2 * (t1 - t2) < 0 ∧ a3 * (t1 - t3) < 0 ∧ -t1 < 0) ∨
        (0 < a0 * (t1 - t0) ∧ 0 < (1 : ℝ) ∧ 0 < -t1 ∧
          a2 * (t1 - t2) < 0 ∧ a3 * (t1 - t3) < 0))) := by
  refine ⟨ordered_ratio_vector_identity v0 v1 v2 v3 q r
      a0 a1 a2 a3 t0 t1 t2 t3 hq hr, ?_, ?_⟩
  · exact ordered_ratio_scalar_identity a0 a1 a2 a3 t0 t1 t2 t3 ha hat
  · exact ordered_ratio_sign_pattern a0 a2 a3 t0 t1 t2 t3
      ha0 ha2 ha3 h01 h12 h23 ht1

end FanoLowerBound
