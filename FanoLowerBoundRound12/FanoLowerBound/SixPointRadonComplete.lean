import FanoLowerBound.DirectSixPointBranches

/-!
# Complete six-point strict Radon lemma in dimension three

Every six points in `ℝ³` for which every four are affinely independent contain
five points admitting a strict `2--3` Radon equality.  The proof classifies the
nonzero barycentric coordinates of the fifth point relative to the first four.
-/

namespace FanoLowerBound

private theorem sum_fin4_complete {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  abel

/-- Six points in general position in `ℝ³` contain a strict `2--3` Radon
subconfiguration on five of the six points. -/
theorem sixPoint_generalPosition_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    HasStrictRadon23 p := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  have hq0 : ∑ i, b.coord i (p 4) • b i = p 4 :=
    b.linear_combination_coord_eq_self (p 4)
  have hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3 := by
    rw [← hq0]
    rw [sum_fin4_complete]
    rfl
  have hasum0 := b.sum_coord_apply_eq_one (p 4)
  have ha : a0 + a1 + a2 + a3 = 1 := by
    calc
      a0 + a1 + a2 + a3 = ∑ i, b.coord i (p 4) := by rw [sum_fin4_complete]
      _ = 1 := hasum0
  have hne0 : a0 ≠ 0 := by
    simpa [a0, b] using fifth_coord_ne_zero p hgp 0
  have hne1 : a1 ≠ 0 := by
    simpa [a1, b] using fifth_coord_ne_zero p hgp 1
  have hne2 : a2 ≠ 0 := by
    simpa [a2, b] using fifth_coord_ne_zero p hgp 2
  have hne3 : a3 ≠ 0 := by
    simpa [a3, b] using fifth_coord_ne_zero p hgp 3

  by_cases h0 : 0 < a0
  · by_cases h1 : 0 < a1
    · by_cases h2 : 0 < a2
      · by_cases h3 : 0 < a3
        · apply allPositive_sixPoint_hasStrictRadon23 p hgp
          intro i
          fin_cases i
          · simpa [a0, b] using h0
          · simpa [a1, b] using h1
          · simpa [a2, b] using h2
          · simpa [a3, b] using h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact threePositiveNeg3_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1 h2 h3n
      · have h2n : a2 < 0 := lt_of_le_of_ne (le_of_not_gt h2) hne2
        by_cases h3 : 0 < a3
        · exact threePositiveNeg2_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1 h2n h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact twoPositive01_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1 h2n h3n
    · have h1n : a1 < 0 := lt_of_le_of_ne (le_of_not_gt h1) hne1
      by_cases h2 : 0 < a2
      · by_cases h3 : 0 < a3
        · exact threePositiveNeg1_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1n h2 h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact twoPositive02_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1n h2 h3n
      · have h2n : a2 < 0 := lt_of_le_of_ne (le_of_not_gt h2) hne2
        by_cases h3 : 0 < a3
        · exact twoPositive03_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0 h1n h2n h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact onePositive0_sixPoint_hasStrictRadon23 p hgp
            (by simpa [a0, b] using h0)
            (by simpa [a1, b] using h1n)
            (by simpa [a2, b] using h2n)
            (by simpa [a3, b] using h3n)
  · have h0n : a0 < 0 := lt_of_le_of_ne (le_of_not_gt h0) hne0
    by_cases h1 : 0 < a1
    · by_cases h2 : 0 < a2
      · by_cases h3 : 0 < a3
        · exact threePositiveNeg0_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0n h1 h2 h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact twoPositive12_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0n h1 h2 h3n
      · have h2n : a2 < 0 := lt_of_le_of_ne (le_of_not_gt h2) hne2
        by_cases h3 : 0 < a3
        · exact twoPositive13_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0n h1 h2n h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact onePositive1_sixPoint_hasStrictRadon23 p hgp
            (by simpa [a0, b] using h0n)
            (by simpa [a1, b] using h1)
            (by simpa [a2, b] using h2n)
            (by simpa [a3, b] using h3n)
    · have h1n : a1 < 0 := lt_of_le_of_ne (le_of_not_gt h1) hne1
      by_cases h2 : 0 < a2
      · by_cases h3 : 0 < a3
        · exact twoPositive23_sixPoint_hasStrictRadon23
            p a0 a1 a2 a3 hq ha h0n h1n h2 h3
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exact onePositive2_sixPoint_hasStrictRadon23 p hgp
            (by simpa [a0, b] using h0n)
            (by simpa [a1, b] using h1n)
            (by simpa [a2, b] using h2)
            (by simpa [a3, b] using h3n)
      · have h2n : a2 < 0 := lt_of_le_of_ne (le_of_not_gt h2) hne2
        by_cases h3 : 0 < a3
        · exact onePositive3_sixPoint_hasStrictRadon23 p hgp
            (by simpa [a0, b] using h0n)
            (by simpa [a1, b] using h1n)
            (by simpa [a2, b] using h2n)
            (by simpa [a3, b] using h3)
        · have h3n : a3 < 0 := lt_of_le_of_ne (le_of_not_gt h3) hne3
          exfalso
          linarith [ha]

#print axioms sixPoint_generalPosition_hasStrictRadon23

end FanoLowerBound
