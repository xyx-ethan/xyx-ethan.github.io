import FanoLowerBound.SunflowerSegment
import Mathlib.Analysis.Convex.Visible

/-!
# Exit boundary of an open set along a segment

Let `p` lie outside an open set `C` and let `c` lie inside `C`.  Along the
segment from `p` to `c`, there is a last parameter outside `C`; every strictly
later parameter up to the endpoint lies in `C`.

The geometric existence step is obtained from Mathlib's closed-set visible
point theorem applied to `Cᶜ`.  The second theorem converts its weak-between
point into the exact `τ ∈ [0,1)` parameterization used in the sunflower
line-core proof.
-/

namespace FanoLowerBound

open AffineMap Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- `τ` is the last parameter outside `C` along the line map from `p` to `c`:
`τ ∈ [0,1)`, the point at `τ` is outside, and all points with parameter in
`(τ,1]` are inside. -/
def IsLastOutsideParameter (C : Set E) (p c : E) (τ : ℝ) : Prop :=
  τ ∈ Ico (0 : ℝ) 1 ∧
    lineMap p c τ ∉ C ∧
    ∀ t ∈ Ioc τ 1, lineMap p c t ∈ C

/-- An open set has an exit-boundary point on every segment from an interior
point to an exterior point.  The boundary point itself is exterior, while all
points strictly between the interior endpoint and the boundary point remain
inside the open set. -/
theorem exists_boundaryPoint_between_inside_outside
    {C : Set E} (hC : IsOpen C) {p c : E} (hp : p ∉ C) (hc : c ∈ C) :
    ∃ q : E,
      q ∉ C ∧
      Wbtw ℝ c q p ∧
      ∀ z : E, Sbtw ℝ c z q → z ∈ C := by
  have hpcompl : p ∈ Cᶜ := by simpa using hp
  obtain ⟨q, hqcompl, hcqp, hvisible⟩ :=
    hC.isClosed_compl.exists_wbtw_isVisible hpcompl c
  refine ⟨q, ?_, hcqp, ?_⟩
  · simpa using hqcompl
  · intro z hz
    by_contra hzC
    exact (hvisible (by simpa using hzC)) hz

/-- Parameter form of `exists_boundaryPoint_between_inside_outside`.
There is a genuine last exterior parameter `τ < 1`; every point with parameter
in `(τ,1]` belongs to the open set. -/
theorem exists_lastOutsideParameter
    {C : Set E} (hC : IsOpen C) {p c : E} (hp : p ∉ C) (hc : c ∈ C) :
    ∃ τ : ℝ, IsLastOutsideParameter C p c τ := by
  obtain ⟨q, hq, hcqp, hinterior⟩ :=
    exists_boundaryPoint_between_inside_outside hC hp hc
  rcases hcqp with ⟨δ, hδ, hδq⟩
  have hδne : δ ≠ 0 := by
    intro hδ0
    have hqc : q = c := by
      simpa [hδ0] using hδq.symm
    exact hq (hqc.symm ▸ hc)
  have hδpos : 0 < δ := lt_of_le_of_ne hδ.1 (Ne.symm hδne)
  refine ⟨1 - δ, ?_⟩
  refine ⟨⟨sub_nonneg.mpr hδ.2, sub_lt_self 1 hδpos⟩, ?_, ?_⟩
  · rw [lineMap_apply_one_sub, hδq]
    exact hq
  · intro t ht
    let u : ℝ := 1 - t
    have hu0 : 0 ≤ u := by
      dsimp [u]
      linarith [ht.2]
    have huδ : u < δ := by
      dsimp [u]
      linarith [ht.1]
    have hmap : lineMap p c t = lineMap c p u := by
      dsimp [u]
      exact (lineMap_apply_one_sub c p t).symm
    rw [hmap]
    by_cases hu : u = 0
    · simpa [hu] using hc
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
      have hcqne : c ≠ q := by
        intro hcq
        exact hq (hcq ▸ hc)
      have hline_ne : c ≠ lineMap c p δ := by
        intro h
        exact hcqne (h.trans hδq)
      have hratio : u / δ ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hupos hδpos, (div_lt_one hδpos).2 huδ⟩
      have hs0 :
          Sbtw ℝ c
            (lineMap c (lineMap c p δ) (u / δ))
            (lineMap c p δ) :=
        (sbtw_lineMap_iff).2 ⟨hline_ne, hratio⟩
      have hs : Sbtw ℝ c (lineMap c p u) q := by
        simpa [lineMap_lineMap_right, div_mul_cancel₀ u hδne, hδq] using hs0
      exact hinterior _ hs

#print axioms exists_boundaryPoint_between_inside_outside
#print axioms exists_lastOutsideParameter

end FanoLowerBound
