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
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `2 mod 6` in the first residual family has divisor `13`. -/
theorem thirteen_dvd_residualFamilyOne_two_add_six_mul (k : ℕ) :
    13 ∣ residualFamilyOne (2 + 6 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 6 2 13 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `5 mod 8` in the first residual family has divisor `73`. -/
theorem seventyThree_dvd_residualFamilyOne_five_add_eight_mul (k : ℕ) :
    73 ∣ residualFamilyOne (5 + 8 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 8 5 73 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `6 mod 16` in the first residual family has divisor `17`. -/
theorem seventeen_dvd_residualFamilyOne_six_add_sixteen_mul (k : ℕ) :
    17 ∣ residualFamilyOne (6 + 16 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 16 6 17 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `13 mod 22` in the first residual family has divisor `23`. -/
theorem twentyThree_dvd_residualFamilyOne_thirteen_add_twentyTwo_mul (k : ℕ) :
    23 ∣ residualFamilyOne (13 + 22 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 22 13 23 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `19 mod 28` in the first residual family has divisor `29`. -/
theorem twentyNine_dvd_residualFamilyOne_nineteen_add_twentyEight_mul (k : ℕ) :
    29 ∣ residualFamilyOne (19 + 28 * k) := by
  simpa [residualFamilyOne] using
    dvd_residual_of_period 740 2391 136 199 28 19 29 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `1 mod 8` in the second residual family has divisor `17`. -/
theorem seventeen_dvd_residualFamilyTwo_one_add_eight_mul (k : ℕ) :
    17 ∣ residualFamilyTwo (1 + 8 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 8 1 17 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `7 mod 14` in the second residual family has divisor `29`. -/
theorem twentyNine_dvd_residualFamilyTwo_seven_add_fourteen_mul (k : ℕ) :
    29 ∣ residualFamilyTwo (7 + 14 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 14 7 29 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `6 mod 16` in the second residual family has divisor `97`. -/
theorem ninetySeven_dvd_residualFamilyTwo_six_add_sixteen_mul (k : ℕ) :
    97 ∣ residualFamilyTwo (6 + 16 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 16 6 97 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `11 mod 18` in the second residual family has divisor `109`. -/
theorem oneHundredNine_dvd_residualFamilyTwo_eleven_add_eighteen_mul (k : ℕ) :
    109 ∣ residualFamilyTwo (11 + 18 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 18 11 109 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `3 mod 13` in the second residual family has divisor `157`. -/
theorem oneFiftySeven_dvd_residualFamilyTwo_three_add_thirteen_mul (k : ℕ) :
    157 ∣ residualFamilyTwo (3 + 13 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 13 3 157 k
      (by decide +kernel) (by decide +kernel)

/-- Every term with index `7 mod 13` in the second residual family has divisor `53`. -/
theorem fiftyThree_dvd_residualFamilyTwo_seven_add_thirteen_mul (k : ℕ) :
    53 ∣ residualFamilyTwo (7 + 13 * k) := by
  simpa [residualFamilyTwo] using
    dvd_residual_of_period 370 2177 666 930 13 7 53 k
      (by decide +kernel) (by decide +kernel)

private lemma not_prime_of_dvd_lt {p n : ℕ} (hp : p ≠ 1)
    (hdiv : p ∣ n) (hlt : p < n) : ¬ n.Prime := by
  intro hn
  have hEq : n = p := (hn.dvd_iff_eq hp).mp hdiv
  omega

/-- Every term in the first residual family is larger than every fixed divisor used above. -/
theorem twoHundredEleven_lt_residualFamilyOne (t : ℕ) :
    211 < residualFamilyOne t := by
  rw [residualFamilyOne, Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2391)]
  have hExp : 3 ≤ 136 + 199 * t := by omega
  have hPow : 10 ^ 3 ≤ 10 ^ (136 + 199 * t) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 10) hExp
  have hMul : 740 * 10 ^ 3 ≤ 740 * 10 ^ (136 + 199 * t) :=
    Nat.mul_le_mul_left 740 hPow
  have hConst : 211 * 2391 < 740 * 10 ^ 3 + 1 := by norm_num
  exact hConst.trans_le (Nat.add_le_add_right hMul 1)

/-- Every term in the second residual family is larger than every fixed divisor used above. -/
theorem oneFiftySeven_lt_residualFamilyTwo (t : ℕ) :
    157 < residualFamilyTwo t := by
  rw [residualFamilyTwo, Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2177)]
  have hExp : 3 ≤ 666 + 930 * t := by omega
  have hPow : 10 ^ 3 ≤ 10 ^ (666 + 930 * t) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 10) hExp
  have hMul : 370 * 10 ^ 3 ≤ 370 * 10 ^ (666 + 930 * t) :=
    Nat.mul_le_mul_left 370 hPow
  have hConst : 157 * 2177 < 370 * 10 ^ 3 + 1 := by norm_num
  exact hConst.trans_le (Nat.add_le_add_right hMul 1)

private lemma residualFamilyOne_not_prime_of_dvd {p t : ℕ}
    (hp : p ≠ 1) (hpBound : p ≤ 211) (hdiv : p ∣ residualFamilyOne t) :
    ¬ (residualFamilyOne t).Prime :=
  not_prime_of_dvd_lt hp hdiv
    (lt_of_le_of_lt hpBound (twoHundredEleven_lt_residualFamilyOne t))

private lemma residualFamilyTwo_not_prime_of_dvd {p t : ℕ}
    (hp : p ≠ 1) (hpBound : p ≤ 157) (hdiv : p ∣ residualFamilyTwo t) :
    ¬ (residualFamilyTwo t).Prime :=
  not_prime_of_dvd_lt hp hdiv
    (lt_of_le_of_lt hpBound (oneFiftySeven_lt_residualFamilyTwo t))

/-- The first residual family is composite on indices `0 mod 6`. -/
theorem residualFamilyOne_six_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (6 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (seven_dvd_residualFamilyOne_six_mul k)

/-- The first residual family is composite on indices `2 mod 6`. -/
theorem residualFamilyOne_two_add_six_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (2 + 6 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (thirteen_dvd_residualFamilyOne_two_add_six_mul k)

/-- The first residual family is composite on indices `5 mod 8`. -/
theorem residualFamilyOne_five_add_eight_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (5 + 8 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (seventyThree_dvd_residualFamilyOne_five_add_eight_mul k)

/-- The first residual family is composite on indices `6 mod 16`. -/
theorem residualFamilyOne_six_add_sixteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (6 + 16 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (seventeen_dvd_residualFamilyOne_six_add_sixteen_mul k)

/-- The first residual family is composite on indices `13 mod 22`. -/
theorem residualFamilyOne_thirteen_add_twentyTwo_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (13 + 22 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (twentyThree_dvd_residualFamilyOne_thirteen_add_twentyTwo_mul k)

/-- The first residual family is composite on indices `19 mod 28`. -/
theorem residualFamilyOne_nineteen_add_twentyEight_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyOne (19 + 28 * k)).Prime :=
  residualFamilyOne_not_prime_of_dvd (by norm_num) (by norm_num)
    (twentyNine_dvd_residualFamilyOne_nineteen_add_twentyEight_mul k)

/-- The second residual family is composite on indices `1 mod 8`. -/
theorem residualFamilyTwo_one_add_eight_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (1 + 8 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (seventeen_dvd_residualFamilyTwo_one_add_eight_mul k)

/-- The second residual family is composite on indices `7 mod 14`. -/
theorem residualFamilyTwo_seven_add_fourteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (7 + 14 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (twentyNine_dvd_residualFamilyTwo_seven_add_fourteen_mul k)

/-- The second residual family is composite on indices `6 mod 16`. -/
theorem residualFamilyTwo_six_add_sixteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (6 + 16 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (ninetySeven_dvd_residualFamilyTwo_six_add_sixteen_mul k)

/-- The second residual family is composite on indices `11 mod 18`. -/
theorem residualFamilyTwo_eleven_add_eighteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (11 + 18 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (oneHundredNine_dvd_residualFamilyTwo_eleven_add_eighteen_mul k)

/-- The second residual family is composite on indices `3 mod 13`. -/
theorem residualFamilyTwo_three_add_thirteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (3 + 13 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (oneFiftySeven_dvd_residualFamilyTwo_three_add_thirteen_mul k)

/-- The second residual family is composite on indices `7 mod 13`. -/
theorem residualFamilyTwo_seven_add_thirteen_mul_not_prime (k : ℕ) :
    ¬ (residualFamilyTwo (7 + 13 * k)).Prime :=
  residualFamilyTwo_not_prime_of_dvd (by norm_num) (by norm_num)
    (fiftyThree_dvd_residualFamilyTwo_seven_add_thirteen_mul k)

end OeisA67599
