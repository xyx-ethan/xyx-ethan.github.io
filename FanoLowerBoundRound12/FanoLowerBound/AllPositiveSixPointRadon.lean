import FanoLowerBound.SixPointRatioPairs
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The all-positive barycentric branch of the six-point Radon lemma

When the fifth point has four positive barycentric coordinates relative to the
first-four affine basis, sort the four sixth-over-fifth coordinate ratios.
Their pairwise distinctness makes the sorted tuple strictly increasing. The
second ratio is nonzero, so the ordered ratio circuit yields an explicit strict
`2--3` Radon equality on five of the six original points.
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

/-- In the all-positive fifth-point branch, a sorted permutation of the four
ratios produces a strict Radon `2--3` witness among five original points. -/
theorem allPositive_sixPoint_strictRadon23
    (p : Fin 6 → Point3)
    (hgp : ∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e))
    (hapos : ∀ i : Fin 4,
      0 < (firstFourAffineBasis p hgp).coord i (p 4)) :
    ∃ σ : Equiv.Perm (Fin 4),
      StrictRadon23
          (firstFourAffineBasis p hgp (σ 0)) (p 5) (p 4)
          (firstFourAffineBasis p hgp (σ 2))
          (firstFourAffineBasis p hgp (σ 3)) ∨
      StrictRadon23
          (firstFourAffineBasis p hgp (σ 2))
          (firstFourAffineBasis p hgp (σ 3))
          (firstFourAffineBasis p hgp (σ 0)) (p 5) (p 4) := by
  let b := firstFourAffineBasis p hgp
  let a : Fin 4 → ℝ := fun i => b.coord i (p 4)
  let c : Fin 4 → ℝ := fun i => b.coord i (p 5)
  let t : Fin 4 → ℝ := sixPointRatio p hgp
  let σ : Equiv.Perm (Fin 4) := Tuple.sort t

  have htinj : Function.Injective t := by
    simpa [t] using sixPointRatio_injective p hgp
  have hsorted : StrictMono (t ∘ σ) :=
    (Tuple.monotone_sort t).strictMono_of_injective
      (htinj.comp σ.injective)
  have h01 : t (σ 0) < t (σ 1) := hsorted (by decide)
  have h12 : t (σ 1) < t (σ 2) := hsorted (by decide)
  have h23 : t (σ 2) < t (σ 3) := hsorted (by decide)

  have hq0 : p 4 = ∑ i, a i • b i := by
    symm
    simpa [a] using b.linear_combination_coord_eq_self (p 4)
  have hr0 : p 5 = ∑ i, c i • b i := by
    symm
    simpa [c] using b.linear_combination_coord_eq_self (p 5)
  have ha0 : ∑ i, a i = 1 := by
    simpa [a] using b.sum_coord_apply_eq_one (p 4)
  have hc0 : ∑ i, c i = 1 := by
    simpa [c] using b.sum_coord_apply_eq_one (p 5)

  have hmul (i : Fin 4) : a i * t i = c i := by
    dsimp [a, c, t, sixPointRatio, b]
    field_simp [fifth_coord_ne_zero p hgp i]

  have hqperm : p 4 = ∑ j, a (σ j) • b (σ j) := by
    calc
      p 4 = ∑ i, a i • b i := hq0
      _ = ∑ j, a (σ j) • b (σ j) := by
        simpa using
          (Equiv.sum_comp σ (fun i : Fin 4 => a i • b i)).symm
  have hrperm : p 5 = ∑ j, (a (σ j) * t (σ j)) • b (σ j) := by
    calc
      p 5 = ∑ i, c i • b i := hr0
      _ = ∑ j, c (σ j) • b (σ j) := by
        simpa using
          (Equiv.sum_comp σ (fun i : Fin 4 => c i • b i)).symm
      _ = ∑ j, (a (σ j) * t (σ j)) • b (σ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hmul]
  have haperm : ∑ j, a (σ j) = 1 := by
    calc
      ∑ j, a (σ j) = ∑ i, a i := Equiv.sum_comp σ a
      _ = 1 := ha0
  have hatperm : ∑ j, a (σ j) * t (σ j) = 1 := by
    calc
      ∑ j, a (σ j) * t (σ j) = ∑ j, c (σ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hmul]
      _ = ∑ i, c i := Equiv.sum_comp σ c
      _ = 1 := hc0

  have hq : p 4 =
      a (σ 0) • b (σ 0) + a (σ 1) • b (σ 1) +
      a (σ 2) • b (σ 2) + a (σ 3) • b (σ 3) := by
    calc
      p 4 = ∑ j, a (σ j) • b (σ j) := hqperm
      _ = _ := sum_fin4 _
  have hr : p 5 =
      (a (σ 0) * t (σ 0)) • b (σ 0) +
      (a (σ 1) * t (σ 1)) • b (σ 1) +
      (a (σ 2) * t (σ 2)) • b (σ 2) +
      (a (σ 3) * t (σ 3)) • b (σ 3) := by
    calc
      p 5 = ∑ j, (a (σ j) * t (σ j)) • b (σ j) := hrperm
      _ = _ := sum_fin4 _
  have ha : a (σ 0) + a (σ 1) + a (σ 2) + a (σ 3) = 1 := by
    calc
      a (σ 0) + a (σ 1) + a (σ 2) + a (σ 3) =
          ∑ j : Fin 4, a (σ j) := by
            symm
            exact sum_fin4 (fun j : Fin 4 => a (σ j))
      _ = 1 := haperm
  have hat :
      a (σ 0) * t (σ 0) + a (σ 1) * t (σ 1) +
      a (σ 2) * t (σ 2) + a (σ 3) * t (σ 3) = 1 := by
    calc
      a (σ 0) * t (σ 0) + a (σ 1) * t (σ 1) +
          a (σ 2) * t (σ 2) + a (σ 3) * t (σ 3) =
        ∑ j : Fin 4, a (σ j) * t (σ j) := by
          symm
          exact sum_fin4 (fun j : Fin 4 => a (σ j) * t (σ j))
      _ = 1 := hatperm

  have haσ0 : 0 < a (σ 0) := by simpa [a, b] using hapos (σ 0)
  have haσ2 : 0 < a (σ 2) := by simpa [a, b] using hapos (σ 2)
  have haσ3 : 0 < a (σ 3) := by simpa [a, b] using hapos (σ 3)
  have htσ1 : t (σ 1) ≠ 0 := by
    simpa [t, sixPointRatio] using
      sixth_over_fifth_coord_ne_zero p hgp (σ 1)

  refine ⟨σ, ?_⟩
  exact ordered_ratio_circuit_strictRadon23
    (b (σ 0)) (b (σ 1)) (b (σ 2)) (b (σ 3)) (p 4) (p 5)
    (a (σ 0)) (a (σ 1)) (a (σ 2)) (a (σ 3))
    (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3))
    hq hr ha hat haσ0 haσ2 haσ3 h01 h12 h23 htσ1

#print axioms allPositive_sixPoint_strictRadon23

end FanoLowerBound
