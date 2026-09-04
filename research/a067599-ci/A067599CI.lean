import FormalConjectures.OEIS.«67599»

/-!
# Integration checks and periodic divisors for OEIS A067599

The pinned Formal Conjectures dependency is patched in CI with the squarefree exclusion theorem.
This file checks that integration and proves fixed-divisor congruences for residue families left
by the exact two-prime-factor reduction.
-/

namespace OeisA67599

example {n : ℕ} (hn : 2 ≤ n) (hsq : Squarefree n) : n < a n :=
  lt_a_of_squarefree hn hsq

example {n : ℕ} (hn : 2 ≤ n) (hsq : Squarefree n) : a n ≠ n :=
  a_ne_of_squarefree hn hsq

/-- The first residual family from the exact two-prime-factor reduction. -/
def residualFamilyOne (t : ℕ) : ℕ :=
  (740 * 10 ^ (136 + 199 * t) + 1) / 2391

/-- The second residual family from the exact two-prime-factor reduction. -/
def residualFamilyTwo (t : ℕ) : ℕ :=
  (370 * 10 ^ (666 + 930 * t) + 1) / 2177

/-- A fixed divisor propagates along a residue class once the decimal multiplier has the
required period modulo the denominator times that divisor. -/
@[category API, AMS 11]
lemma dvd_residual_of_period
    (A D Q0 M m r p k : ℕ)
    (hbase : D * p ∣ A * 10 ^ (Q0 + M * r) + 1)
    (hperiod : 10 ^ (M * m) ≡ 1 [MOD D * p]) :
    p ∣ (A * 10 ^ (Q0 + M * (r + m * k)) + 1) / D := by
  have hperiodPow : 10 ^ ((M * m) * k) ≡ 1 [MOD D * p] := by
    simpa [pow_mul] using hperiod.pow k
  have hmul :
      (A * 10 ^ (Q0 + M * r)) * 10 ^ ((M * m) * k) + 1 ≡
        (A * 10 ^ (Q0 + M * r)) * 1 + 1 [MOD D * p] :=
    (hperiodPow.mul_left (A * 10 ^ (Q0 + M * r))).add_right 1
  have hmul' :
      (A * 10 ^ (Q0 + M * r)) * 10 ^ ((M * m) * k) + 1 ≡
        A * 10 ^ (Q0 + M * r) + 1 [MOD D * p] := by
    simpa using hmul
  have hzero : A * 10 ^ (Q0 + M * r) + 1 ≡ 0 [MOD D * p] :=
    hbase.modEq_zero_nat
  have hcong : A * 10 ^ (Q0 + M * (r + m * k)) + 1 ≡ 0 [MOD D * p] := by
    simpa [Nat.mul_add, pow_add, Nat.mul_assoc] using hmul'.trans hzero
  have hDp : D * p ∣ A * 10 ^ (Q0 + M * (r + m * k)) + 1 :=
    Nat.modEq_zero_iff_dvd.mp hcong
  have hD : D ∣ A * 10 ^ (Q0 + M * (r + m * k)) + 1 :=
    dvd_trans (by exact ⟨p, rfl⟩) hDp
  exact (Nat.dvd_div_iff_mul_dvd hD).2 hDp

/-- Every term with index `0 mod 6` in the first residual family has divisor `7`. -/
theorem seven_dvd_residualFamilyOne_six_mul (k : ℕ) :
    7 ∣ residualFamilyOne (6 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 6 0 7 k
      (by norm_num) (by norm_num [Nat.ModEq])

/-- Every term with index `2 mod 6` in the first residual family has divisor `13`. -/
theorem thirteen_dvd_residualFamilyOne_two_add_six_mul (k : ℕ) :
    13 ∣ residualFamilyOne (2 + 6 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 6 2 13 k
      (by norm_num) (by norm_num [Nat.ModEq])

/-- Every term with index `5 mod 8` in the first residual family has divisor `73`. -/
theorem seventyThree_dvd_residualFamilyOne_five_add_eight_mul (k : ℕ) :
    73 ∣ residualFamilyOne (5 + 8 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 8 5 73 k
      (by norm_num) (by norm_num [Nat.ModEq])

/-- Every term with index `1 mod 8` in the second residual family has divisor `17`. -/
theorem seventeen_dvd_residualFamilyTwo_one_add_eight_mul (k : ℕ) :
    17 ∣ residualFamilyTwo (1 + 8 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 8 1 17 k
      (by norm_num) (by norm_num [Nat.ModEq])

/-- Every term with index `3 mod 13` in the second residual family has divisor `157`. -/
theorem oneFiftySeven_dvd_residualFamilyTwo_three_add_thirteen_mul (k : ℕ) :
    157 ∣ residualFamilyTwo (3 + 13 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 13 3 157 k
      (by norm_num) (by norm_num [Nat.ModEq])

/-- Every term with index `7 mod 13` in the second residual family has divisor `53`. -/
theorem fiftyThree_dvd_residualFamilyTwo_seven_add_thirteen_mul (k : ℕ) :
    53 ∣ residualFamilyTwo (7 + 13 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 13 7 53 k
      (by norm_num) (by norm_num [Nat.ModEq])

end OeisA67599
