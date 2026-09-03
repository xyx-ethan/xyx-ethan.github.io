import FanoLowerBound.RatioDistinctness
import FanoLowerBound.SixthCoordinates

/-!
# Barycentric-ratio inequalities for six generally positioned points

This file begins the finite instantiation of the generic ratio-collision lemma.
The first theorem proves the `0,1` ratio inequality directly from the four-point
general-position instance indexed by `[5,4,2,3]`.
-/

namespace FanoLowerBound

private theorem sum_fin4 {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  ac_rfl

/-- The four points `p₅,p₄,p₂,p₃`. -/
def ratioPairEmb01 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 2, 3]
  inj' := by decide

/-- The zeroth and first barycentric ratios of `p₅` over `p₄`, relative to the
first-four affine basis, are unequal. -/
theorem sixPoint_ratio01_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    (firstFourAffineBasis p hgp).coord 0 (p 5) /
        (firstFourAffineBasis p hgp).coord 0 (p 4) ≠
      (firstFourAffineBasis p hgp).coord 1 (p 5) /
        (firstFourAffineBasis p hgp).coord 1 (p 4) := by
  let b := firstFourAffineBasis p hgp
  let a0 := b.coord 0 (p 4)
  let a1 := b.coord 1 (p 4)
  let a2 := b.coord 2 (p 4)
  let a3 := b.coord 3 (p 4)
  let c0 := b.coord 0 (p 5)
  let c1 := b.coord 1 (p 5)
  let c2 := b.coord 2 (p 5)
  let c3 := b.coord 3 (p 5)
  have hq0 := b.linear_combination_coord_eq_self (p 4)
  have hr0 := b.linear_combination_coord_eq_self (p 5)
  have hqsum : a0 • b 0 + a1 • b 1 + a2 • b 2 + a3 • b 3 = p 4 := by
    calc
      a0 • b 0 + a1 • b 1 + a2 • b 2 + a3 • b 3 =
          ∑ i, b.coord i (p 4) • b i := by
            rw [sum_fin4]
            rfl
      _ = p 4 := hq0
  have hrsum : c0 • b 0 + c1 • b 1 + c2 • b 2 + c3 • b 3 = p 5 := by
    calc
      c0 • b 0 + c1 • b 1 + c2 • b 2 + c3 • b 3 =
          ∑ i, b.coord i (p 5) • b i := by
            rw [sum_fin4]
            rfl
      _ = p 5 := hr0
  have hq : p 4 = a0 • b 0 + a1 • b 1 + a2 • b 2 + a3 • b 3 := hqsum.symm
  have hr : p 5 = c0 • b 0 + c1 • b 1 + c2 • b 2 + c3 • b 3 := hrsum.symm
  have ha0 := b.sum_coord_apply_eq_one (p 4)
  have hc0 := b.sum_coord_apply_eq_one (p 5)
  have ha : a0 + a1 + a2 + a3 = 1 := by
    calc
      a0 + a1 + a2 + a3 = ∑ i, b.coord i (p 4) := by
        rw [sum_fin4]
        rfl
      _ = 1 := ha0
  have hc : c0 + c1 + c2 + c3 = 1 := by
    calc
      c0 + c1 + c2 + c3 = ∑ i, b.coord i (p 5) := by
        rw [sum_fin4]
        rfl
      _ = 1 := hc0
  have hfun : (![p 5, p 4, b 2, b 3] : Fin 4 → Point3) =
      p ∘ ratioPairEmb01 := by
    funext j
    fin_cases j <;> rfl
  have hfour : AffineIndependent ℝ (![p 5, p 4, b 2, b 3] : Fin 4 → Point3) := by
    rw [hfun]
    exact hgp ratioPairEmb01
  change c0 / a0 ≠ c1 / a1
  exact ratio01_ne_of_four_affineIndependent
    (b 0) (b 1) (b 2) (b 3) (p 4) (p 5)
    a0 a1 a2 a3 c0 c1 c2 c3 hq hr ha hc
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 1)
    (fifth_coord_ne_zero p hgp 2) (fifth_coord_ne_zero p hgp 3) hfour

#print axioms sixPoint_ratio01_ne

end FanoLowerBound
