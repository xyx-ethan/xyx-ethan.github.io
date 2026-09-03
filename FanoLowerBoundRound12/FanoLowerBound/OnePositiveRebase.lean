import FanoLowerBound.AllPositiveSixPointRadon

/-!
# Rebase for the one-positive barycentric branch

If the fifth point has exactly one positive barycentric coordinate relative to
four affine-basis points, solve for the corresponding basis point. It becomes
a strict convex combination of the fifth point and the other three basis
points. Reindexing these four points as a new affine basis reduces the branch
to the already certified all-positive six-point Radon theorem.
-/

namespace FanoLowerBound

private theorem sum_fin4 {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  abel

/-- A strict `2--3` Radon equality on five distinct entries of a six-tuple,
encoded by a permutation of all six entries and a permutation of the four basis slots. -/
def HasStrictRadon23 (p : Fin 6 → Point3) : Prop :=
  ∃ τ : Equiv.Perm (Fin 6), ∃ σ : Equiv.Perm (Fin 4),
    StrictRadon23
        ((p ∘ τ) (baseEmb (σ 0))) ((p ∘ τ) 5) ((p ∘ τ) 4)
        ((p ∘ τ) (baseEmb (σ 2))) ((p ∘ τ) (baseEmb (σ 3))) ∨
    StrictRadon23
        ((p ∘ τ) (baseEmb (σ 2))) ((p ∘ τ) (baseEmb (σ 3)))
        ((p ∘ τ) (baseEmb (σ 0))) ((p ∘ τ) 5) ((p ∘ τ) 4)

/-- Transport a strict Radon subconfiguration through a permutation. -/
theorem hasStrictRadon23_of_comp_perm
    (p : Fin 6 → Point3) (τ : Equiv.Perm (Fin 6))
    (h : HasStrictRadon23 (p ∘ τ)) :
    HasStrictRadon23 p := by
  rcases h with ⟨ρ, σ, h⟩
  refine ⟨ρ.trans τ, σ, ?_⟩
  simpa [Function.comp_def] using h

/-- Package the all-positive theorem as existence of a five-point subconfiguration. -/
theorem allPositive_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (hapos : ∀ i : Fin 4,
      0 < (firstFourAffineBasis p hgp).coord i (p 4)) :
    HasStrictRadon23 p := by
  rcases allPositive_sixPoint_strictRadon23 p hgp hapos with ⟨σ, h⟩
  refine ⟨Equiv.refl _, σ, ?_⟩
  simpa [firstFourAffineBasis_apply, Function.comp_def] using h

/-- General position is invariant under reindexing by a permutation. -/
theorem generalPosition_comp_perm
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (τ : Equiv.Perm (Fin 6)) :
    ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ ((p ∘ τ) ∘ e) := by
  intro e
  let e' : Fin 4 ↪ Fin 6 :=
    { toFun := fun i => τ (e i)
      inj' := τ.injective.comp e.injective }
  have h := hgp e'
  simpa [e', Function.comp_def] using h

/-- Coordinates of an affine-basis expansion are unique. -/
theorem affineBasis_coord_eq_of_linearCombination
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : AffineBasis (Fin 4) ℝ E) (q : E) (w : Fin 4 → ℝ)
    (hwsum : ∑ i, w i = 1)
    (hwcomb : ∑ i, w i • b i = q) (i : Fin 4) :
    b.coord i q = w i := by
  let c : Fin 4 → ℝ := fun j => b.coord j q
  have hcsum : ∑ j, c j = 1 := by
    simpa [c] using b.sum_coord_apply_eq_one q
  have hccomb : ∑ j, c j • b j = q := by
    simpa [c] using b.linear_combination_coord_eq_self q
  have hcaff : Finset.univ.affineCombination ℝ b c = q := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hcsum]
    exact hccomb
  have hwaff : Finset.univ.affineCombination ℝ b w = q := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hwsum]
    exact hwcomb
  have hcw : c = w :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ b).1
      b.ind' c w hcsum hwsum (hcaff.trans hwaff.symm)
  exact congrFun hcw i

/-- Reindex `[p₀,p₁,p₂,p₃,p₄,p₅]` as `[p₄,p₁,p₂,p₃,p₀,p₅]`. -/
def rebasePerm0 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 3, 0, 5]
  invFun := ![4, 1, 2, 3, 0, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Canonical one-positive branch: only the zeroth fifth-point coordinate is positive. -/
theorem onePositive0_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (ha0 : 0 < (firstFourAffineBasis p hgp).coord 0 (p 4))
    (ha1 : (firstFourAffineBasis p hgp).coord 1 (p 4) < 0)
    (ha2 : (firstFourAffineBasis p hgp).coord 2 (p 4) < 0)
    (ha3 : (firstFourAffineBasis p hgp).coord 3 (p 4) < 0) :
    HasStrictRadon23 p := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  let p' : Fin 6 → Point3 := p ∘ rebasePerm0
  have hgp' : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p' ∘ e) := by
    simpa [p'] using generalPosition_comp_perm p hgp rebasePerm0
  let b' := firstFourAffineBasis p' hgp'
  let w : Fin 4 → ℝ := ![1 / a0, (-a1) / a0, (-a2) / a0, (-a3) / a0]

  have hq0 : ∑ i, b.coord i (p 4) • b i = p 4 :=
    b.linear_combination_coord_eq_self (p 4)
  have hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3 := by
    rw [← hq0]
    rw [sum_fin4]
    rfl
  have hasum0 := b.sum_coord_apply_eq_one (p 4)
  have hasum : a0 + a1 + a2 + a3 = 1 := by
    rw [← hasum0]
    rw [sum_fin4]
    rfl
  have ha0' : 0 < a0 := by simpa [a0, b] using ha0
  have ha1' : a1 < 0 := by simpa [a1, b] using ha1
  have ha2' : a2 < 0 := by simpa [a2, b] using ha2
  have ha3' : a3 < 0 := by simpa [a3, b] using ha3
  have ha0ne : a0 ≠ 0 := ne_of_gt ha0'

  have hwsum : ∑ i, w i = 1 := by
    rw [sum_fin4]
    dsimp [w]
    field_simp [ha0ne] <;> linarith [hasum]
  have hwcomb : ∑ i, w i • b' i = p' 4 := by
    rw [sum_fin4]
    change (1 / a0) • p 4 + ((-a1) / a0) • p 1 +
        ((-a2) / a0) • p 2 + ((-a3) / a0) • p 3 = p 0
    rw [hq]
    field_simp [ha0ne]
    module
  have hapos' : ∀ i : Fin 4, 0 < b'.coord i (p' 4) := by
    intro i
    rw [affineBasis_coord_eq_of_linearCombination b' (p' 4) w hwsum hwcomb i]
    fin_cases i
    · exact div_pos zero_lt_one ha0'
    · exact div_pos (neg_pos.mpr ha1') ha0'
    · exact div_pos (neg_pos.mpr ha2') ha0'
    · exact div_pos (neg_pos.mpr ha3') ha0'
  apply hasStrictRadon23_of_comp_perm p rebasePerm0
  exact allPositive_sixPoint_hasStrictRadon23 p' hgp' hapos'

#print axioms affineBasis_coord_eq_of_linearCombination
#print axioms onePositive0_sixPoint_hasStrictRadon23

end FanoLowerBound
