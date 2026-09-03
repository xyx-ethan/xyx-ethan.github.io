import FanoLowerBound.RatioDistinctness
import FanoLowerBound.SixthCoordinates

/-!
# All barycentric-ratio inequalities for six generally positioned points

For six points in general position in `ℝ³`, use the first four as an affine
basis, and divide the barycentric coordinates of the sixth point by those of
the fifth. This file proves that all four resulting ratios are pairwise
distinct. Each of the six unordered pairs is certified by the complementary
four-point general-position instance.
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

/-- The barycentric-coordinate ratio of the sixth point over the fifth point,
relative to the affine basis formed by the first four points. -/
noncomputable def sixPointRatio
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) : ℝ :=
  (firstFourAffineBasis p hgp).coord i (p 5) /
    (firstFourAffineBasis p hgp).coord i (p 4)

/-- Explicit four-term expansion of the fifth point. -/
theorem fifth_explicit_expansion
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    p 4 =
      (firstFourAffineBasis p hgp).coord 0 (p 4) •
          firstFourAffineBasis p hgp 0 +
      (firstFourAffineBasis p hgp).coord 1 (p 4) •
          firstFourAffineBasis p hgp 1 +
      (firstFourAffineBasis p hgp).coord 2 (p 4) •
          firstFourAffineBasis p hgp 2 +
      (firstFourAffineBasis p hgp).coord 3 (p 4) •
          firstFourAffineBasis p hgp 3 := by
  let b := firstFourAffineBasis p hgp
  have h := b.linear_combination_coord_eq_self (p 4)
  symm
  calc
    b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
        b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 =
      ∑ i, b.coord i (p 4) • b i := by rw [sum_fin4]
    _ = p 4 := h

/-- Explicit four-term expansion of the sixth point. -/
theorem sixth_explicit_expansion
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    p 5 =
      (firstFourAffineBasis p hgp).coord 0 (p 5) •
          firstFourAffineBasis p hgp 0 +
      (firstFourAffineBasis p hgp).coord 1 (p 5) •
          firstFourAffineBasis p hgp 1 +
      (firstFourAffineBasis p hgp).coord 2 (p 5) •
          firstFourAffineBasis p hgp 2 +
      (firstFourAffineBasis p hgp).coord 3 (p 5) •
          firstFourAffineBasis p hgp 3 := by
  let b := firstFourAffineBasis p hgp
  have h := b.linear_combination_coord_eq_self (p 5)
  symm
  calc
    b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
        b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 =
      ∑ i, b.coord i (p 5) • b i := by rw [sum_fin4]
    _ = p 5 := h

/-- Explicit coordinate-sum identity for the fifth point. -/
theorem fifth_explicit_sum
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    (firstFourAffineBasis p hgp).coord 0 (p 4) +
      (firstFourAffineBasis p hgp).coord 1 (p 4) +
      (firstFourAffineBasis p hgp).coord 2 (p 4) +
      (firstFourAffineBasis p hgp).coord 3 (p 4) = 1 := by
  let b := firstFourAffineBasis p hgp
  calc
    b.coord 0 (p 4) + b.coord 1 (p 4) +
        b.coord 2 (p 4) + b.coord 3 (p 4) =
      ∑ i, b.coord i (p 4) := by rw [sum_fin4]
    _ = 1 := b.sum_coord_apply_eq_one (p 4)

/-- Explicit coordinate-sum identity for the sixth point. -/
theorem sixth_explicit_sum
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    (firstFourAffineBasis p hgp).coord 0 (p 5) +
      (firstFourAffineBasis p hgp).coord 1 (p 5) +
      (firstFourAffineBasis p hgp).coord 2 (p 5) +
      (firstFourAffineBasis p hgp).coord 3 (p 5) = 1 := by
  let b := firstFourAffineBasis p hgp
  calc
    b.coord 0 (p 5) + b.coord 1 (p 5) +
        b.coord 2 (p 5) + b.coord 3 (p 5) =
      ∑ i, b.coord i (p 5) := by rw [sum_fin4]
    _ = 1 := b.sum_coord_apply_eq_one (p 5)

/-- Complementary embeddings for the six unordered ratio pairs. -/
def ratioPairEmb01 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 2, 3]
  inj' := by decide

def ratioPairEmb02 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 1, 3]
  inj' := by decide

def ratioPairEmb03 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 1, 2]
  inj' := by decide

def ratioPairEmb12 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 0, 3]
  inj' := by decide

def ratioPairEmb13 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 0, 2]
  inj' := by decide

def ratioPairEmb23 : Fin 4 ↪ Fin 6 where
  toFun := ![5, 4, 0, 1]
  inj' := by decide

private theorem ratio_hfour
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (e : Fin 4 ↪ Fin 6) (x2 x3 : Point3)
    (hfun : (![p 5, p 4, x2, x3] : Fin 4 → Point3) = p ∘ e) :
    AffineIndependent ℝ (![p 5, p 4, x2, x3] : Fin 4 → Point3) := by
  rw [hfun]
  exact hgp e

/-- Ratio pair `(0,1)` is distinct. -/
theorem sixPoint_ratio01_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 0 ≠ sixPointRatio p hgp 1 := by
  let b := firstFourAffineBasis p hgp
  have hq := fifth_explicit_expansion p hgp
  have hr := sixth_explicit_expansion p hgp
  have ha := fifth_explicit_sum p hgp
  have hb := sixth_explicit_sum p hgp
  have hfun : (![p 5, p 4, b 2, b 3] : Fin 4 → Point3) =
      p ∘ ratioPairEmb01 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 0 (p 5) / b.coord 0 (p 4) ≠
    b.coord 1 (p 5) / b.coord 1 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 0) (b 1) (b 2) (b 3) (p 4) (p 5)
    (b.coord 0 (p 4)) (b.coord 1 (p 4))
    (b.coord 2 (p 4)) (b.coord 3 (p 4))
    (b.coord 0 (p 5)) (b.coord 1 (p 5))
    (b.coord 2 (p 5)) (b.coord 3 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 1)
    (fifth_coord_ne_zero p hgp 2) (fifth_coord_ne_zero p hgp 3)
    (ratio_hfour p hgp ratioPairEmb01 (b 2) (b 3) hfun)

/-- Ratio pair `(0,2)` is distinct. -/
theorem sixPoint_ratio02_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 0 ≠ sixPointRatio p hgp 2 := by
  let b := firstFourAffineBasis p hgp
  have hq0 := fifth_explicit_expansion p hgp
  have hr0 := sixth_explicit_expansion p hgp
  have ha0 := fifth_explicit_sum p hgp
  have hb0 := sixth_explicit_sum p hgp
  have hq : p 4 = b.coord 0 (p 4) • b 0 + b.coord 2 (p 4) • b 2 +
      b.coord 1 (p 4) • b 1 + b.coord 3 (p 4) • b 3 := by
    calc
      p 4 = b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
          b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 := hq0
      _ = _ := by module
  have hr : p 5 = b.coord 0 (p 5) • b 0 + b.coord 2 (p 5) • b 2 +
      b.coord 1 (p 5) • b 1 + b.coord 3 (p 5) • b 3 := by
    calc
      p 5 = b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
          b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 := hr0
      _ = _ := by module
  have ha : b.coord 0 (p 4) + b.coord 2 (p 4) +
      b.coord 1 (p 4) + b.coord 3 (p 4) = 1 := by linarith
  have hb : b.coord 0 (p 5) + b.coord 2 (p 5) +
      b.coord 1 (p 5) + b.coord 3 (p 5) = 1 := by linarith
  have hfun : (![p 5, p 4, b 1, b 3] : Fin 4 → Point3) =
      p ∘ ratioPairEmb02 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 0 (p 5) / b.coord 0 (p 4) ≠
    b.coord 2 (p 5) / b.coord 2 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 0) (b 2) (b 1) (b 3) (p 4) (p 5)
    (b.coord 0 (p 4)) (b.coord 2 (p 4))
    (b.coord 1 (p 4)) (b.coord 3 (p 4))
    (b.coord 0 (p 5)) (b.coord 2 (p 5))
    (b.coord 1 (p 5)) (b.coord 3 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 2)
    (fifth_coord_ne_zero p hgp 1) (fifth_coord_ne_zero p hgp 3)
    (ratio_hfour p hgp ratioPairEmb02 (b 1) (b 3) hfun)

/-- Ratio pair `(0,3)` is distinct. -/
theorem sixPoint_ratio03_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 0 ≠ sixPointRatio p hgp 3 := by
  let b := firstFourAffineBasis p hgp
  have hq0 := fifth_explicit_expansion p hgp
  have hr0 := sixth_explicit_expansion p hgp
  have ha0 := fifth_explicit_sum p hgp
  have hb0 := sixth_explicit_sum p hgp
  have hq : p 4 = b.coord 0 (p 4) • b 0 + b.coord 3 (p 4) • b 3 +
      b.coord 1 (p 4) • b 1 + b.coord 2 (p 4) • b 2 := by
    calc
      p 4 = b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
          b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 := hq0
      _ = _ := by module
  have hr : p 5 = b.coord 0 (p 5) • b 0 + b.coord 3 (p 5) • b 3 +
      b.coord 1 (p 5) • b 1 + b.coord 2 (p 5) • b 2 := by
    calc
      p 5 = b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
          b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 := hr0
      _ = _ := by module
  have ha : b.coord 0 (p 4) + b.coord 3 (p 4) +
      b.coord 1 (p 4) + b.coord 2 (p 4) = 1 := by linarith
  have hb : b.coord 0 (p 5) + b.coord 3 (p 5) +
      b.coord 1 (p 5) + b.coord 2 (p 5) = 1 := by linarith
  have hfun : (![p 5, p 4, b 1, b 2] : Fin 4 → Point3) =
      p ∘ ratioPairEmb03 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 0 (p 5) / b.coord 0 (p 4) ≠
    b.coord 3 (p 5) / b.coord 3 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 0) (b 3) (b 1) (b 2) (p 4) (p 5)
    (b.coord 0 (p 4)) (b.coord 3 (p 4))
    (b.coord 1 (p 4)) (b.coord 2 (p 4))
    (b.coord 0 (p 5)) (b.coord 3 (p 5))
    (b.coord 1 (p 5)) (b.coord 2 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 3)
    (fifth_coord_ne_zero p hgp 1) (fifth_coord_ne_zero p hgp 2)
    (ratio_hfour p hgp ratioPairEmb03 (b 1) (b 2) hfun)

/-- Ratio pair `(1,2)` is distinct. -/
theorem sixPoint_ratio12_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 1 ≠ sixPointRatio p hgp 2 := by
  let b := firstFourAffineBasis p hgp
  have hq0 := fifth_explicit_expansion p hgp
  have hr0 := sixth_explicit_expansion p hgp
  have ha0 := fifth_explicit_sum p hgp
  have hb0 := sixth_explicit_sum p hgp
  have hq : p 4 = b.coord 1 (p 4) • b 1 + b.coord 2 (p 4) • b 2 +
      b.coord 0 (p 4) • b 0 + b.coord 3 (p 4) • b 3 := by
    calc
      p 4 = b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
          b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 := hq0
      _ = _ := by module
  have hr : p 5 = b.coord 1 (p 5) • b 1 + b.coord 2 (p 5) • b 2 +
      b.coord 0 (p 5) • b 0 + b.coord 3 (p 5) • b 3 := by
    calc
      p 5 = b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
          b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 := hr0
      _ = _ := by module
  have ha : b.coord 1 (p 4) + b.coord 2 (p 4) +
      b.coord 0 (p 4) + b.coord 3 (p 4) = 1 := by linarith
  have hb : b.coord 1 (p 5) + b.coord 2 (p 5) +
      b.coord 0 (p 5) + b.coord 3 (p 5) = 1 := by linarith
  have hfun : (![p 5, p 4, b 0, b 3] : Fin 4 → Point3) =
      p ∘ ratioPairEmb12 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 1 (p 5) / b.coord 1 (p 4) ≠
    b.coord 2 (p 5) / b.coord 2 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 1) (b 2) (b 0) (b 3) (p 4) (p 5)
    (b.coord 1 (p 4)) (b.coord 2 (p 4))
    (b.coord 0 (p 4)) (b.coord 3 (p 4))
    (b.coord 1 (p 5)) (b.coord 2 (p 5))
    (b.coord 0 (p 5)) (b.coord 3 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 1) (fifth_coord_ne_zero p hgp 2)
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 3)
    (ratio_hfour p hgp ratioPairEmb12 (b 0) (b 3) hfun)

/-- Ratio pair `(1,3)` is distinct. -/
theorem sixPoint_ratio13_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 1 ≠ sixPointRatio p hgp 3 := by
  let b := firstFourAffineBasis p hgp
  have hq0 := fifth_explicit_expansion p hgp
  have hr0 := sixth_explicit_expansion p hgp
  have ha0 := fifth_explicit_sum p hgp
  have hb0 := sixth_explicit_sum p hgp
  have hq : p 4 = b.coord 1 (p 4) • b 1 + b.coord 3 (p 4) • b 3 +
      b.coord 0 (p 4) • b 0 + b.coord 2 (p 4) • b 2 := by
    calc
      p 4 = b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
          b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 := hq0
      _ = _ := by module
  have hr : p 5 = b.coord 1 (p 5) • b 1 + b.coord 3 (p 5) • b 3 +
      b.coord 0 (p 5) • b 0 + b.coord 2 (p 5) • b 2 := by
    calc
      p 5 = b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
          b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 := hr0
      _ = _ := by module
  have ha : b.coord 1 (p 4) + b.coord 3 (p 4) +
      b.coord 0 (p 4) + b.coord 2 (p 4) = 1 := by linarith
  have hb : b.coord 1 (p 5) + b.coord 3 (p 5) +
      b.coord 0 (p 5) + b.coord 2 (p 5) = 1 := by linarith
  have hfun : (![p 5, p 4, b 0, b 2] : Fin 4 → Point3) =
      p ∘ ratioPairEmb13 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 1 (p 5) / b.coord 1 (p 4) ≠
    b.coord 3 (p 5) / b.coord 3 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 1) (b 3) (b 0) (b 2) (p 4) (p 5)
    (b.coord 1 (p 4)) (b.coord 3 (p 4))
    (b.coord 0 (p 4)) (b.coord 2 (p 4))
    (b.coord 1 (p 5)) (b.coord 3 (p 5))
    (b.coord 0 (p 5)) (b.coord 2 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 1) (fifth_coord_ne_zero p hgp 3)
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 2)
    (ratio_hfour p hgp ratioPairEmb13 (b 0) (b 2) hfun)

/-- Ratio pair `(2,3)` is distinct. -/
theorem sixPoint_ratio23_ne
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    sixPointRatio p hgp 2 ≠ sixPointRatio p hgp 3 := by
  let b := firstFourAffineBasis p hgp
  have hq0 := fifth_explicit_expansion p hgp
  have hr0 := sixth_explicit_expansion p hgp
  have ha0 := fifth_explicit_sum p hgp
  have hb0 := sixth_explicit_sum p hgp
  have hq : p 4 = b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 +
      b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 := by
    calc
      p 4 = b.coord 0 (p 4) • b 0 + b.coord 1 (p 4) • b 1 +
          b.coord 2 (p 4) • b 2 + b.coord 3 (p 4) • b 3 := hq0
      _ = _ := by module
  have hr : p 5 = b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 +
      b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 := by
    calc
      p 5 = b.coord 0 (p 5) • b 0 + b.coord 1 (p 5) • b 1 +
          b.coord 2 (p 5) • b 2 + b.coord 3 (p 5) • b 3 := hr0
      _ = _ := by module
  have ha : b.coord 2 (p 4) + b.coord 3 (p 4) +
      b.coord 0 (p 4) + b.coord 1 (p 4) = 1 := by linarith
  have hb : b.coord 2 (p 5) + b.coord 3 (p 5) +
      b.coord 0 (p 5) + b.coord 1 (p 5) = 1 := by linarith
  have hfun : (![p 5, p 4, b 0, b 1] : Fin 4 → Point3) =
      p ∘ ratioPairEmb23 := by
    funext j
    fin_cases j <;> rfl
  change b.coord 2 (p 5) / b.coord 2 (p 4) ≠
    b.coord 3 (p 5) / b.coord 3 (p 4)
  exact ratio01_ne_of_four_affineIndependent
    (b 2) (b 3) (b 0) (b 1) (p 4) (p 5)
    (b.coord 2 (p 4)) (b.coord 3 (p 4))
    (b.coord 0 (p 4)) (b.coord 1 (p 4))
    (b.coord 2 (p 5)) (b.coord 3 (p 5))
    (b.coord 0 (p 5)) (b.coord 1 (p 5))
    hq hr ha hb
    (fifth_coord_ne_zero p hgp 2) (fifth_coord_ne_zero p hgp 3)
    (fifth_coord_ne_zero p hgp 0) (fifth_coord_ne_zero p hgp 1)
    (ratio_hfour p hgp ratioPairEmb23 (b 0) (b 1) hfun)

/-- The four barycentric ratios are pairwise distinct. -/
theorem sixPointRatio_injective
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    Function.Injective (sixPointRatio p hgp) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso; exact sixPoint_ratio01_ne p hgp hij
  · exfalso; exact sixPoint_ratio02_ne p hgp hij
  · exfalso; exact sixPoint_ratio03_ne p hgp hij
  · exfalso; exact sixPoint_ratio01_ne p hgp hij.symm
  · rfl
  · exfalso; exact sixPoint_ratio12_ne p hgp hij
  · exfalso; exact sixPoint_ratio13_ne p hgp hij
  · exfalso; exact sixPoint_ratio02_ne p hgp hij.symm
  · exfalso; exact sixPoint_ratio12_ne p hgp hij.symm
  · rfl
  · exfalso; exact sixPoint_ratio23_ne p hgp hij
  · exfalso; exact sixPoint_ratio03_ne p hgp hij.symm
  · exfalso; exact sixPoint_ratio13_ne p hgp hij.symm
  · exfalso; exact sixPoint_ratio23_ne p hgp hij.symm
  · rfl

#print axioms sixPoint_ratio01_ne
#print axioms sixPoint_ratio02_ne
#print axioms sixPoint_ratio03_ne
#print axioms sixPoint_ratio12_ne
#print axioms sixPoint_ratio13_ne
#print axioms sixPoint_ratio23_ne
#print axioms sixPointRatio_injective

end FanoLowerBound
