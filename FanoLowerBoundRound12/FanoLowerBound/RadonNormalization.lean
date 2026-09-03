import FanoLowerBound.RatioCircuitCore

/-!
# Normalizing the ordered ratio circuit to a strict 3--2 Radon witness

This file turns the signed affine dependence from `ordered_ratio_circuit_core`
into two explicit strict convex combinations with the same value. It is the
geometric bridge between the ratio arithmetic and a 3--2 Radon partition.
-/

namespace FanoLowerBound

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `StrictRadon23 x₀ x₁ y₀ y₁ y₂` means that a strict convex combination of
`x₀,x₁` equals a strict convex combination of `y₀,y₁,y₂`. -/
def StrictRadon23 (x0 x1 y0 y1 y2 : E) : Prop :=
  ∃ a0 a1 b0 b1 b2 : ℝ,
    0 < a0 ∧ 0 < a1 ∧ 0 < b0 ∧ 0 < b1 ∧ 0 < b2 ∧
    a0 + a1 = 1 ∧ b0 + b1 + b2 = 1 ∧
    a0 • x0 + a1 • x1 = b0 • y0 + b1 • y1 + b2 • y2

/-- The ordered ratio circuit gives a strict 2-versus-3 Radon equality on the
five points `v₀,r,q,v₂,v₃`; the omitted point is `v₁`. Which side has two
points is determined by the sign of the second ordered ratio `t₁`. -/
theorem ordered_ratio_circuit_strictRadon23
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
    StrictRadon23 v0 r q v2 v3 ∨ StrictRadon23 v2 v3 v0 r q := by
  obtain ⟨hvec, hscalar, hsign⟩ := ordered_ratio_circuit_core
    v0 v1 v2 v3 q r a0 a1 a2 a3 t0 t1 t2 t3
    hq hr ha hat ha0 ha2 ha3 h01 h12 h23 ht1
  rcases hsign with hpositive | hnegative
  · rcases hpositive with ⟨hc0, hone, hc2, hc3, hqt⟩
    have ht1pos : 0 < t1 := by linarith
    let c0 : ℝ := a0 * (t1 - t0)
    let c2 : ℝ := a2 * (t1 - t2)
    let c3 : ℝ := a3 * (t1 - t3)
    let S : ℝ := c0 + 1
    have hc0' : 0 < c0 := by simpa [c0] using hc0
    have hc2' : c2 < 0 := by simpa [c2] using hc2
    have hc3' : c3 < 0 := by simpa [c3] using hc3
    have hS : 0 < S := by dsimp [S]; linarith
    have hSne : S ≠ 0 := ne_of_gt hS
    have hsum : t1 + (-c2) + (-c3) = S := by
      dsimp [c0, c2, c3, S] at *
      linarith
    have hvec' : r - t1 • q + c0 • v0 + c2 • v2 + c3 • v3 = 0 := by
      simpa [c0, c2, c3] using hvec
    have hcomb : c0 • v0 + (1 : ℝ) • r =
        t1 • q + (-c2) • v2 + (-c3) • v3 := by
      rw [← sub_eq_zero]
      calc
        (c0 • v0 + (1 : ℝ) • r) -
              (t1 • q + (-c2) • v2 + (-c3) • v3) =
            r - t1 • q + c0 • v0 + c2 • v2 + c3 • v3 := by module
        _ = 0 := hvec'
    left
    refine ⟨c0 / S, 1 / S, t1 / S, (-c2) / S, (-c3) / S,
      div_pos hc0' hS, div_pos zero_lt_one hS, div_pos ht1pos hS,
      div_pos (neg_pos.mpr hc2') hS, div_pos (neg_pos.mpr hc3') hS, ?_, ?_, ?_⟩
    · rw [← add_div, show c0 + 1 = S by rfl, div_self hSne]
    · rw [← add_div, ← add_div, hsum, div_self hSne]
    · have hs := congrArg (fun z : E => (1 / S) • z) hcomb
      simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hs
  · rcases hnegative with ⟨hc0, hone, hqt, hc2, hc3⟩
    have ht1neg : t1 < 0 := by linarith
    let c0 : ℝ := a0 * (t1 - t0)
    let c2 : ℝ := a2 * (t1 - t2)
    let c3 : ℝ := a3 * (t1 - t3)
    let S : ℝ := (-c2) + (-c3)
    have hc0' : 0 < c0 := by simpa [c0] using hc0
    have hc2' : c2 < 0 := by simpa [c2] using hc2
    have hc3' : c3 < 0 := by simpa [c3] using hc3
    have hS : 0 < S := by dsimp [S]; linarith
    have hSne : S ≠ 0 := ne_of_gt hS
    have hsum : c0 + 1 + (-t1) = S := by
      dsimp [c0, c2, c3, S] at *
      linarith
    have hvec' : r - t1 • q + c0 • v0 + c2 • v2 + c3 • v3 = 0 := by
      simpa [c0, c2, c3] using hvec
    have hbase : c0 • v0 + (1 : ℝ) • r =
        t1 • q + (-c2) • v2 + (-c3) • v3 := by
      rw [← sub_eq_zero]
      calc
        (c0 • v0 + (1 : ℝ) • r) -
              (t1 • q + (-c2) • v2 + (-c3) • v3) =
            r - t1 • q + c0 • v0 + c2 • v2 + c3 • v3 := by module
        _ = 0 := hvec'
    have hcomb : (-c2) • v2 + (-c3) • v3 =
        c0 • v0 + (1 : ℝ) • r + (-t1) • q := by
      rw [← sub_eq_zero]
      have hz : (c0 • v0 + (1 : ℝ) • r) -
          (t1 • q + (-c2) • v2 + (-c3) • v3) = 0 := sub_eq_zero.mpr hbase
      calc
        ((-c2) • v2 + (-c3) • v3) -
              (c0 • v0 + (1 : ℝ) • r + (-t1) • q) =
            -((c0 • v0 + (1 : ℝ) • r) -
              (t1 • q + (-c2) • v2 + (-c3) • v3)) := by module
        _ = 0 := by rw [hz]; simp
    right
    refine ⟨(-c2) / S, (-c3) / S, c0 / S, 1 / S, (-t1) / S,
      div_pos (neg_pos.mpr hc2') hS, div_pos (neg_pos.mpr hc3') hS,
      div_pos hc0' hS, div_pos zero_lt_one hS, div_pos (neg_pos.mpr ht1neg) hS,
      ?_, ?_, ?_⟩
    · rw [← add_div, show -c2 + -c3 = S by rfl, div_self hSne]
    · rw [← add_div, ← add_div, hsum, div_self hSne]
    · have hs := congrArg (fun z : E => (1 / S) • z) hcomb
      simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hs

#print axioms ordered_ratio_circuit_strictRadon23

end FanoLowerBound
