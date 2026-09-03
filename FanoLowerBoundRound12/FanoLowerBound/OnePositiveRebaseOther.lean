import FanoLowerBound.OnePositiveRebase

/-!
# Remaining one-positive barycentric rebase branches

The unique positive fifth-point coordinate may occupy basis slot `1`, `2`, or
`3`.  Each branch reindexes the six points so the fifth point and the other
three basis points become the new affine basis, and the omitted old basis point
has four strictly positive coordinates.
-/

namespace FanoLowerBound

private theorem sum_fin4_other {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  abel

/-- Reindex for the branch whose unique positive coordinate is `1`. -/
def rebasePerm1 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 3, 1, 5]
  invFun := ![1, 4, 2, 3, 0, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- One-positive branch with unique positive coordinate `1`. -/
theorem onePositive1_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (ha0 : (firstFourAffineBasis p hgp).coord 0 (p 4) < 0)
    (ha1 : 0 < (firstFourAffineBasis p hgp).coord 1 (p 4))
    (ha2 : (firstFourAffineBasis p hgp).coord 2 (p 4) < 0)
    (ha3 : (firstFourAffineBasis p hgp).coord 3 (p 4) < 0) :
    HasStrictRadon23 p := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  let p' : Fin 6 → Point3 := p ∘ rebasePerm1
  have hgp' : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p' ∘ e) := by
    simpa [p'] using generalPosition_comp_perm p hgp rebasePerm1
  let b' := firstFourAffineBasis p' hgp'
  let w : Fin 4 → ℝ := ![1 / a1, (-a0) / a1, (-a2) / a1, (-a3) / a1]
  have hq0 : ∑ i, b.coord i (p 4) • b i = p 4 :=
    b.linear_combination_coord_eq_self (p 4)
  have hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3 := by
    rw [← hq0]
    rw [sum_fin4_other]
    rfl
  have hasum0 := b.sum_coord_apply_eq_one (p 4)
  have hasum : a0 + a1 + a2 + a3 = 1 := by
    calc
      a0 + a1 + a2 + a3 = ∑ i, b.coord i (p 4) := by rw [sum_fin4_other]
      _ = 1 := hasum0
  have ha0' : a0 < 0 := by simpa [a0, b] using ha0
  have ha1' : 0 < a1 := by simpa [a1, b] using ha1
  have ha2' : a2 < 0 := by simpa [a2, b] using ha2
  have ha3' : a3 < 0 := by simpa [a3, b] using ha3
  have ha1ne : a1 ≠ 0 := ne_of_gt ha1'
  have hwsum : ∑ i, w i = 1 := by
    rw [sum_fin4_other]
    dsimp [w]
    field_simp [ha1ne] <;> linarith [hasum]
  have h11 : (1 / a1) * a1 = 1 := by field_simp [ha1ne]
  have h10 : (1 / a1) * a0 + (-a0) / a1 = 0 := by
    field_simp [ha1ne] <;> ring
  have h12 : (1 / a1) * a2 + (-a2) / a1 = 0 := by
    field_simp [ha1ne] <;> ring
  have h13 : (1 / a1) * a3 + (-a3) / a1 = 0 := by
    field_simp [ha1ne] <;> ring
  have hwcomb : ∑ i, w i • b' i = p' 4 := by
    rw [sum_fin4_other]
    change (1 / a1) • p 4 + ((-a0) / a1) • p 0 +
        ((-a2) / a1) • p 2 + ((-a3) / a1) • p 3 = p 1
    rw [hq]
    simp only [smul_add, smul_smul]
    rw [h11]
    simp only [one_smul]
    module
  have hapos' : ∀ i : Fin 4, 0 < b'.coord i (p' 4) := by
    intro i
    rw [affineBasis_coord_eq_of_linearCombination b' (p' 4) w hwsum hwcomb i]
    fin_cases i
    · exact div_pos zero_lt_one ha1'
    · exact div_pos (neg_pos.mpr ha0') ha1'
    · exact div_pos (neg_pos.mpr ha2') ha1'
    · exact div_pos (neg_pos.mpr ha3') ha1'
  apply hasStrictRadon23_of_comp_perm p rebasePerm1
  exact allPositive_sixPoint_hasStrictRadon23 p' hgp' hapos'

/-- Reindex for the branch whose unique positive coordinate is `2`. -/
def rebasePerm2 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 2, 5]
  invFun := ![1, 2, 4, 3, 0, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- One-positive branch with unique positive coordinate `2`. -/
theorem onePositive2_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (ha0 : (firstFourAffineBasis p hgp).coord 0 (p 4) < 0)
    (ha1 : (firstFourAffineBasis p hgp).coord 1 (p 4) < 0)
    (ha2 : 0 < (firstFourAffineBasis p hgp).coord 2 (p 4))
    (ha3 : (firstFourAffineBasis p hgp).coord 3 (p 4) < 0) :
    HasStrictRadon23 p := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  let p' : Fin 6 → Point3 := p ∘ rebasePerm2
  have hgp' : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p' ∘ e) := by
    simpa [p'] using generalPosition_comp_perm p hgp rebasePerm2
  let b' := firstFourAffineBasis p' hgp'
  let w : Fin 4 → ℝ := ![1 / a2, (-a0) / a2, (-a1) / a2, (-a3) / a2]
  have hq0 : ∑ i, b.coord i (p 4) • b i = p 4 :=
    b.linear_combination_coord_eq_self (p 4)
  have hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3 := by
    rw [← hq0]
    rw [sum_fin4_other]
    rfl
  have hasum0 := b.sum_coord_apply_eq_one (p 4)
  have hasum : a0 + a1 + a2 + a3 = 1 := by
    calc
      a0 + a1 + a2 + a3 = ∑ i, b.coord i (p 4) := by rw [sum_fin4_other]
      _ = 1 := hasum0
  have ha0' : a0 < 0 := by simpa [a0, b] using ha0
  have ha1' : a1 < 0 := by simpa [a1, b] using ha1
  have ha2' : 0 < a2 := by simpa [a2, b] using ha2
  have ha3' : a3 < 0 := by simpa [a3, b] using ha3
  have ha2ne : a2 ≠ 0 := ne_of_gt ha2'
  have hwsum : ∑ i, w i = 1 := by
    rw [sum_fin4_other]
    dsimp [w]
    field_simp [ha2ne] <;> linarith [hasum]
  have h22 : (1 / a2) * a2 = 1 := by field_simp [ha2ne]
  have h20 : (1 / a2) * a0 + (-a0) / a2 = 0 := by
    field_simp [ha2ne] <;> ring
  have h21 : (1 / a2) * a1 + (-a1) / a2 = 0 := by
    field_simp [ha2ne] <;> ring
  have h23 : (1 / a2) * a3 + (-a3) / a2 = 0 := by
    field_simp [ha2ne] <;> ring
  have hwcomb : ∑ i, w i • b' i = p' 4 := by
    rw [sum_fin4_other]
    change (1 / a2) • p 4 + ((-a0) / a2) • p 0 +
        ((-a1) / a2) • p 1 + ((-a3) / a2) • p 3 = p 2
    rw [hq]
    simp only [smul_add, smul_smul]
    rw [h22]
    simp only [one_smul]
    module
  have hapos' : ∀ i : Fin 4, 0 < b'.coord i (p' 4) := by
    intro i
    rw [affineBasis_coord_eq_of_linearCombination b' (p' 4) w hwsum hwcomb i]
    fin_cases i
    · exact div_pos zero_lt_one ha2'
    · exact div_pos (neg_pos.mpr ha0') ha2'
    · exact div_pos (neg_pos.mpr ha1') ha2'
    · exact div_pos (neg_pos.mpr ha3') ha2'
  apply hasStrictRadon23_of_comp_perm p rebasePerm2
  exact allPositive_sixPoint_hasStrictRadon23 p' hgp' hapos'

/-- Reindex for the branch whose unique positive coordinate is `3`. -/
def rebasePerm3 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- One-positive branch with unique positive coordinate `3`. -/
theorem onePositive3_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (ha0 : (firstFourAffineBasis p hgp).coord 0 (p 4) < 0)
    (ha1 : (firstFourAffineBasis p hgp).coord 1 (p 4) < 0)
    (ha2 : (firstFourAffineBasis p hgp).coord 2 (p 4) < 0)
    (ha3 : 0 < (firstFourAffineBasis p hgp).coord 3 (p 4)) :
    HasStrictRadon23 p := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  let p' : Fin 6 → Point3 := p ∘ rebasePerm3
  have hgp' : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p' ∘ e) := by
    simpa [p'] using generalPosition_comp_perm p hgp rebasePerm3
  let b' := firstFourAffineBasis p' hgp'
  let w : Fin 4 → ℝ := ![1 / a3, (-a0) / a3, (-a1) / a3, (-a2) / a3]
  have hq0 : ∑ i, b.coord i (p 4) • b i = p 4 :=
    b.linear_combination_coord_eq_self (p 4)
  have hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3 := by
    rw [← hq0]
    rw [sum_fin4_other]
    rfl
  have hasum0 := b.sum_coord_apply_eq_one (p 4)
  have hasum : a0 + a1 + a2 + a3 = 1 := by
    calc
      a0 + a1 + a2 + a3 = ∑ i, b.coord i (p 4) := by rw [sum_fin4_other]
      _ = 1 := hasum0
  have ha0' : a0 < 0 := by simpa [a0, b] using ha0
  have ha1' : a1 < 0 := by simpa [a1, b] using ha1
  have ha2' : a2 < 0 := by simpa [a2, b] using ha2
  have ha3' : 0 < a3 := by simpa [a3, b] using ha3
  have ha3ne : a3 ≠ 0 := ne_of_gt ha3'
  have hwsum : ∑ i, w i = 1 := by
    rw [sum_fin4_other]
    dsimp [w]
    field_simp [ha3ne] <;> linarith [hasum]
  have h33 : (1 / a3) * a3 = 1 := by field_simp [ha3ne]
  have h30 : (1 / a3) * a0 + (-a0) / a3 = 0 := by
    field_simp [ha3ne] <;> ring
  have h31 : (1 / a3) * a1 + (-a1) / a3 = 0 := by
    field_simp [ha3ne] <;> ring
  have h32 : (1 / a3) * a2 + (-a2) / a3 = 0 := by
    field_simp [ha3ne] <;> ring
  have hwcomb : ∑ i, w i • b' i = p' 4 := by
    rw [sum_fin4_other]
    change (1 / a3) • p 4 + ((-a0) / a3) • p 0 +
        ((-a1) / a3) • p 1 + ((-a2) / a3) • p 2 = p 3
    rw [hq]
    simp only [smul_add, smul_smul]
    rw [h33]
    simp only [one_smul]
    module
  have hapos' : ∀ i : Fin 4, 0 < b'.coord i (p' 4) := by
    intro i
    rw [affineBasis_coord_eq_of_linearCombination b' (p' 4) w hwsum hwcomb i]
    fin_cases i
    · exact div_pos zero_lt_one ha3'
    · exact div_pos (neg_pos.mpr ha0') ha3'
    · exact div_pos (neg_pos.mpr ha1') ha3'
    · exact div_pos (neg_pos.mpr ha2') ha3'
  apply hasStrictRadon23_of_comp_perm p rebasePerm3
  exact allPositive_sixPoint_hasStrictRadon23 p' hgp' hapos'

#print axioms onePositive1_sixPoint_hasStrictRadon23
#print axioms onePositive2_sixPoint_hasStrictRadon23
#print axioms onePositive3_sixPoint_hasStrictRadon23

end FanoLowerBound
