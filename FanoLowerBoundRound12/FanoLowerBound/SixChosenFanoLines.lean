import FanoLowerBound.FanoIndexNormalization
import FanoLowerBound.SixPointRadonComplete
import Mathlib.Data.List.FinRange

/-!
# Consuming the six-point Radon witness on six chosen Fano maximal words

This module bridges the existential encoding `HasStrictRadon23` returned by the
six-point general-position theorem to the arbitrary ordered five-label forcing
theorem from Round 24.  A six-element embedding into the seven Fano maximal
words transports the five distinct source positions to five distinct labels in
`0,...,6`; the two possible Radon orientations are handled separately.
-/

namespace FanoLowerBound

open Set

/-- The source positions used by the first orientation of `HasStrictRadon23`. -/
private def radonSourceLeft
    (σ : Equiv.Perm (Fin 4)) : List (Fin 6) :=
  [baseEmb (σ 0), 5, 4, baseEmb (σ 2), baseEmb (σ 3)]

/-- The source positions used by the second orientation of `HasStrictRadon23`. -/
private def radonSourceRight
    (σ : Equiv.Perm (Fin 4)) : List (Fin 6) :=
  [baseEmb (σ 2), baseEmb (σ 3), baseEmb (σ 0), 5, 4]

private theorem baseEmb_val (i : Fin 4) : (baseEmb i).val = i.val := by
  fin_cases i <;> rfl

private theorem baseEmb_ne_four (i : Fin 4) : baseEmb i ≠ (4 : Fin 6) := by
  intro h
  have hv := congrArg Fin.val h
  rw [baseEmb_val] at hv
  omega

private theorem four_ne_baseEmb (i : Fin 4) : (4 : Fin 6) ≠ baseEmb i :=
  (baseEmb_ne_four i).symm

private theorem baseEmb_ne_five (i : Fin 4) : baseEmb i ≠ (5 : Fin 6) := by
  intro h
  have hv := congrArg Fin.val h
  rw [baseEmb_val] at hv
  omega

private theorem five_ne_baseEmb (i : Fin 4) : (5 : Fin 6) ≠ baseEmb i :=
  (baseEmb_ne_five i).symm

private theorem permutedBase_ne
    (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) :
    baseEmb (σ i) ≠ baseEmb (σ j) := by
  intro h
  exact hij (σ.injective (baseEmb.injective h))

private theorem radonSourceLeft_nodup
    (σ : Equiv.Perm (Fin 4)) : (radonSourceLeft σ).Nodup := by
  have h02 : baseEmb (σ 0) ≠ baseEmb (σ 2) :=
    permutedBase_ne σ (by decide)
  have h03 : baseEmb (σ 0) ≠ baseEmb (σ 3) :=
    permutedBase_ne σ (by decide)
  have h23 : baseEmb (σ 2) ≠ baseEmb (σ 3) :=
    permutedBase_ne σ (by decide)
  simp [radonSourceLeft, List.nodup_cons,
    baseEmb_ne_four, four_ne_baseEmb,
    baseEmb_ne_five, five_ne_baseEmb,
    h02, h03, h23]

private theorem radonSourceRight_nodup
    (σ : Equiv.Perm (Fin 4)) : (radonSourceRight σ).Nodup := by
  have h20 : baseEmb (σ 2) ≠ baseEmb (σ 0) :=
    permutedBase_ne σ (by decide)
  have h23 : baseEmb (σ 2) ≠ baseEmb (σ 3) :=
    permutedBase_ne σ (by decide)
  have h30 : baseEmb (σ 3) ≠ baseEmb (σ 0) :=
    permutedBase_ne σ (by decide)
  simp [radonSourceRight, List.nodup_cons,
    baseEmb_ne_four, four_ne_baseEmb,
    baseEmb_ne_five, five_ne_baseEmb,
    h20, h23, h30]

/-- An embedding into the seven Fano labels, after a six-point permutation,
remains injective after taking the underlying natural-number labels. -/
private theorem mappedLabel_injective
    (ι : Fin 6 ↪ Fin 7) (τ : Equiv.Perm (Fin 6)) :
    Function.Injective (fun t : Fin 6 => (ι (τ t)).val) := by
  intro x y h
  apply τ.injective
  apply ι.injective
  exact Fin.ext h

private theorem mappedLeftLabels_nodup
    (ι : Fin 6 ↪ Fin 7) (τ : Equiv.Perm (Fin 6))
    (σ : Equiv.Perm (Fin 4)) :
    [ (ι (τ (baseEmb (σ 0)))).val,
      (ι (τ 5)).val,
      (ι (τ 4)).val,
      (ι (τ (baseEmb (σ 2)))).val,
      (ι (τ (baseEmb (σ 3)))).val ].Nodup := by
  have h := (radonSourceLeft_nodup σ).map (mappedLabel_injective ι τ)
  simpa [radonSourceLeft] using h

private theorem mappedRightLabels_nodup
    (ι : Fin 6 ↪ Fin 7) (τ : Equiv.Perm (Fin 6))
    (σ : Equiv.Perm (Fin 4)) :
    [ (ι (τ (baseEmb (σ 2)))).val,
      (ι (τ (baseEmb (σ 3)))).val,
      (ι (τ (baseEmb (σ 0)))).val,
      (ι (τ 5)).val,
      (ι (τ 4)).val ].Nodup := by
  have h := (radonSourceRight_nodup σ).map (mappedLabel_injective ι τ)
  simpa [radonSourceRight] using h

/-- A strict Radon witness selected from six distinct Fano maximal-word labels
contradicts the absence of a fivefold active point. -/
theorem sixChosenFanoLines_hasStrictRadon_contradiction
    {U : Nat → Set Point3} {P : Nat → Point3}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : Point3, InThreeCore (U x) (U y) (U z) q)
    (hno5 : NoFiveDistinctActive U)
    (ι : Fin 6 ↪ Fin 7)
    (hrad : HasStrictRadon23 (fun t : Fin 6 => P (ι t).val)) : False := by
  rcases hrad with ⟨τ, σ, hleft | hright⟩
  · apply arbitraryOrderedFive_strictRadon_contradicts_noFiveDistinctActive
      hopen hconv hpoint hsun hcore hno5
      (ι (τ (baseEmb (σ 0)))).isLt
      (ι (τ 5)).isLt
      (ι (τ 4)).isLt
      (ι (τ (baseEmb (σ 2)))).isLt
      (ι (τ (baseEmb (σ 3)))).isLt
      (mappedLeftLabels_nodup ι τ σ)
    simpa [Function.comp_def] using hleft
  · apply arbitraryOrderedFive_strictRadon_contradicts_noFiveDistinctActive
      hopen hconv hpoint hsun hcore hno5
      (ι (τ (baseEmb (σ 2)))).isLt
      (ι (τ (baseEmb (σ 3)))).isLt
      (ι (τ (baseEmb (σ 0)))).isLt
      (ι (τ 5)).isLt
      (ι (τ 4)).isLt
      (mappedRightLabels_nodup ι τ σ)
    simpa [Function.comp_def] using hright

/-- End-to-end finite-geometric bridge: six selected Fano maximal-word points
in general position already contradict the Fano no-fivefold condition. -/
theorem sixChosenFanoLines_generalPosition_contradiction
    {U : Nat → Set Point3} {P : Nat → Point3}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : Point3, InThreeCore (U x) (U y) (U z) q)
    (hno5 : NoFiveDistinctActive U)
    (ι : Fin 6 ↪ Fin 7)
    (hgp : ∀ e : Fin 4 ↪ Fin 6,
      AffineIndependent ℝ ((fun t : Fin 6 => P (ι t).val) ∘ e)) : False := by
  exact sixChosenFanoLines_hasStrictRadon_contradiction
    hopen hconv hpoint hsun hcore hno5 ι
    (sixPoint_generalPosition_hasStrictRadon23
      (fun t : Fin 6 => P (ι t).val) hgp)

#print axioms sixChosenFanoLines_hasStrictRadon_contradiction
#print axioms sixChosenFanoLines_generalPosition_contradiction

end FanoLowerBound
