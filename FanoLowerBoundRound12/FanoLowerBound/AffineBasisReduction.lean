import FanoLowerBound.RadonNormalization
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine-basis reduction for six points in `ℝ³`

This module establishes the first geometric part of the six-point `3--2` Radon lemma:
* four points in general position form an affine basis of `Fin 3 → ℝ`;
* replacing any one basis point by a fifth generally-positioned point remains affine independent;
* consequently every barycentric coordinate of that fifth point is nonzero.

The proof is fully explicit on `Fin 4` and uses four certified embeddings into `Fin 6`.
-/

namespace FanoLowerBound

abbrev Point3 := Fin 3 → ℝ

/-- The first four indices, viewed as an embedding into six indices. -/
def baseEmb : Fin 4 ↪ Fin 6 where
  toFun := ![0, 1, 2, 3]
  inj' := by decide

/-- Replace the first basis index by index `4`. -/
def replaceEmb0 : Fin 4 ↪ Fin 6 where
  toFun := ![4, 1, 2, 3]
  inj' := by decide

/-- Replace the second basis index by index `4`. -/
def replaceEmb1 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 4, 2, 3]
  inj' := by decide

/-- Replace the third basis index by index `4`. -/
def replaceEmb2 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 1, 4, 3]
  inj' := by decide

/-- Replace the fourth basis index by index `4`. -/
def replaceEmb3 : Fin 4 ↪ Fin 6 where
  toFun := ![0, 1, 2, 4]
  inj' := by decide

/-- Four generally-positioned points in `ℝ³` form an affine basis. -/
noncomputable def firstFourAffineBasis
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    AffineBasis (Fin 4) ℝ Point3 where
  toFun := p ∘ baseEmb
  ind' := hgp baseEmb
  tot' := ((hgp baseEmb).affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by
    norm_num [Point3])

@[simp] theorem firstFourAffineBasis_apply
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    firstFourAffineBasis p hgp i = p (baseEmb i) := rfl

/-- Replace one entry of an affine basis by a new point. -/
def replacePoint {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : AffineBasis (Fin 4) ℝ E) (q : E) (i : Fin 4) : Fin 4 → E :=
  fun j => if j = i then q else b j

/-- If replacing the `i`th affine-basis point by `q` remains affine independent,
then the `i`th barycentric coordinate of `q` is nonzero. -/
theorem coord_ne_zero_of_replacePoint_affineIndependent
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : AffineBasis (Fin 4) ℝ E) (q : E) (i : Fin 4)
    (hrep : AffineIndependent ℝ (replacePoint b q i)) :
    b.coord i q ≠ 0 := by
  intro hzero
  let wq : Fin 4 → ℝ := fun j => if j = i then 1 else 0
  let wb : Fin 4 → ℝ := fun j => if j = i then 0 else b.coord j q
  have hwq : ∑ j, wq j = 1 := by
    classical
    simp [wq]
  have hwb : ∑ j, wb j = 1 := by
    classical
    rw [show (∑ j, wb j) = (∑ j, b.coord j q) - b.coord i q by
      simp [wb, Finset.sum_ite_irrel, Finset.filter_ne'])]
    simp [hzero]
  have hcombq : Finset.univ.affineCombination ℝ (replacePoint b q i) wq = q := by
    classical
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hwq]
    simp [wq, replacePoint]
  have hcombb : Finset.univ.affineCombination ℝ (replacePoint b q i) wb = q := by
    classical
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hwb]
    have hbq := b.linear_combination_coord_eq_self q
    rw [← hbq]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [wb, replacePoint, hzero]
    · simp [wb, replacePoint, hji]
  have heq : wq = wb :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ (replacePoint b q i)).1
      hrep wq wb hwq hwb (hcombq.trans hcombb.symm)
  have hi := congrFun heq i
  simp [wq, wb] at hi

/-- The fifth point can replace any one of the first four points without losing affine independence. -/
theorem replacePoint_fifth_affineIndependent
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    AffineIndependent ℝ (replacePoint (firstFourAffineBasis p hgp) (p 4) i) := by
  fin_cases i
  · simpa [replacePoint, firstFourAffineBasis, baseEmb, replaceEmb0,
      Function.comp_def] using hgp replaceEmb0
  · simpa [replacePoint, firstFourAffineBasis, baseEmb, replaceEmb1,
      Function.comp_def] using hgp replaceEmb1
  · simpa [replacePoint, firstFourAffineBasis, baseEmb, replaceEmb2,
      Function.comp_def] using hgp replaceEmb2
  · simpa [replacePoint, firstFourAffineBasis, baseEmb, replaceEmb3,
      Function.comp_def] using hgp replaceEmb3

/-- Every barycentric coordinate of the fifth point with respect to the first four is nonzero. -/
theorem fifth_coord_ne_zero
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (i : Fin 4) :
    (firstFourAffineBasis p hgp).coord i (p 4) ≠ 0 :=
  coord_ne_zero_of_replacePoint_affineIndependent
    (firstFourAffineBasis p hgp) (p 4) i
    (replacePoint_fifth_affineIndependent p hgp i)

/-- The four fifth-point coordinates sum to one. -/
theorem fifth_coord_sum_eq_one
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) :
    ∑ i, (firstFourAffineBasis p hgp).coord i (p 4) = 1 := by
  simpa using (firstFourAffineBasis p hgp).sum_coord_apply_eq_one (p 4)

#print axioms firstFourAffineBasis
#print axioms coord_ne_zero_of_replacePoint_affineIndependent
#print axioms replacePoint_fifth_affineIndependent
#print axioms fifth_coord_ne_zero

end FanoLowerBound
