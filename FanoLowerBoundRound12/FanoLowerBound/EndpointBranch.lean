import FanoLowerBound.ParallelCrossing
import Mathlib.Analysis.Convex.Topology

/-!
# Endpoint branch of the open-convex sunflower line-core proof

If the last point outside the common core on the segment from a core point to
the middle petal point is the middle point itself, then the original
transversal line already meets the common core.  The proof uses the closure of
an open segment, the interior--closure segment theorem for convex sets, and the
openness of the middle petal.
-/

namespace FanoLowerBound

open AffineMap Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- If the open edge `(c,p)` consists of common-core points, then it lies in
`U₁`. -/
theorem openSegment_subset_firstPetal_of_coreEdge
    {U₁ U₂ U₃ : Set E} {c p : E}
    (hcp : c ≠ p)
    (hedge : ∀ y : E, Sbtw ℝ c y p → InThreeCore U₁ U₂ U₃ y) :
    openSegment ℝ c p ⊆ U₁ := by
  intro y hy
  rw [openSegment_eq_image] at hy
  rcases hy with ⟨t, ht, rfl⟩
  have hs : Sbtw ℝ c ((1 - t) • c + t • p) p := by
    simpa [lineMap_apply_module] using
      ((sbtw_lineMap_iff).2 ⟨hcp, ht⟩)
  exact (hedge _ hs).1

/-- Endpoint case.  Assume `p₂` is outside the common core, while every point
strictly between a core point `c` and `p₂` belongs to the core.  Then some
point strictly between `p₁` and `p₂` already belongs to all three petals.

The key step is that `p₂ ∈ closure U₁`; hence the open segment `(p₁,p₂)` lies
in `U₁`.  Since `U₂` is open at `p₂`, it meets this open segment. -/
theorem endpointBoundary_openSegment_hitsCore
    {U₁ U₂ U₃ : Set E}
    (hU₁open : IsOpen U₁) (hU₂open : IsOpen U₂)
    (hU₁conv : Convex ℝ U₁)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    {p₁ p₂ c : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂)
    (hc : InThreeCore U₁ U₂ U₃ c)
    (hp₂not : ¬ InThreeCore U₁ U₂ U₃ p₂)
    (hedge : ∀ y : E, Sbtw ℝ c y p₂ → InThreeCore U₁ U₂ U₃ y) :
    ∃ z : E, InThreeCore U₁ U₂ U₃ z ∧ Sbtw ℝ p₁ z p₂ := by
  have hcp : c ≠ p₂ := by
    intro h
    apply hp₂not
    simpa [h] using hc
  have hp₁p₂ : p₁ ≠ p₂ := by
    intro h
    apply hp₂not
    have hp₂U₁ : p₂ ∈ U₁ := by simpa [h] using hp₁
    exact ⟨hp₂U₁, hp₂, hsun.1 ⟨hp₂U₁, hp₂⟩⟩
  have hedgeU₁ : openSegment ℝ c p₂ ⊆ U₁ :=
    openSegment_subset_firstPetal_of_coreEdge hcp hedge
  have hp₂clEdge : p₂ ∈ closure (openSegment ℝ c p₂) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ c p₂)
  have hp₂clU₁ : p₂ ∈ closure U₁ := closure_mono hedgeU₁ hp₂clEdge
  have hp₁int : p₁ ∈ interior U₁ := by
    simpa [hU₁open.interior_eq] using hp₁
  have hsegInt : openSegment ℝ p₁ p₂ ⊆ interior U₁ :=
    hU₁conv.openSegment_interior_closure_subset_interior hp₁int hp₂clU₁
  have hsegU₁ : openSegment ℝ p₁ p₂ ⊆ U₁ :=
    fun z hz => interior_subset (hsegInt hz)
  have hp₂clSeg : p₂ ∈ closure (openSegment ℝ p₁ p₂) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ p₁ p₂)
  have hmeet : (U₂ ∩ openSegment ℝ p₁ p₂).Nonempty :=
    mem_closure_iff_nhds.mp hp₂clSeg U₂ (hU₂open.mem_nhds hp₂)
  rcases hmeet with ⟨z, hzU₂, hzseg⟩
  have hzU₁ : z ∈ U₁ := hsegU₁ hzseg
  have hzU₃ : z ∈ U₃ := hsun.1 ⟨hzU₁, hzU₂⟩
  have hzs : Sbtw ℝ p₁ z p₂ := by
    rw [openSegment_eq_image] at hzseg
    rcases hzseg with ⟨t, ht, rfl⟩
    simpa [lineMap_apply_module] using
      ((sbtw_lineMap_iff).2 ⟨hp₁p₂, ht⟩)
  exact ⟨z, ⟨hzU₁, hzU₂, hzU₃⟩, hzs⟩

/-- Endpoint case in the geometry used by the sunflower line-core theorem:
if `p₂` is strictly between `p₁,p₃`, the core point found on `(p₁,p₂)` lies
on the original line `p₁p₃`. -/
theorem endpointBoundary_baseLine_hitsCore
    {U₁ U₂ U₃ : Set E}
    (hU₁open : IsOpen U₁) (hU₂open : IsOpen U₂)
    (hU₁conv : Convex ℝ U₁)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    {p₁ p₂ p₃ c : E}
    (hp₂btw : Sbtw ℝ p₁ p₂ p₃)
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂)
    (hc : InThreeCore U₁ U₂ U₃ c)
    (hp₂not : ¬ InThreeCore U₁ U₂ U₃ p₂)
    (hedge : ∀ y : E, Sbtw ℝ c y p₂ → InThreeCore U₁ U₂ U₃ y) :
    ∃ z : E, InThreeCore U₁ U₂ U₃ z ∧ z ∈ line[ℝ, p₁, p₃] := by
  obtain ⟨z, hzcore, hzbtw⟩ :=
    endpointBoundary_openSegment_hitsCore
      hU₁open hU₂open hU₁conv hsun hp₁ hp₂ hc hp₂not hedge
  refine ⟨z, hzcore, ?_⟩
  exact AffineSubspace.mem_of_wbtw hzbtw.1
    (left_mem_affineSpan_pair ℝ p₁ p₃) hp₂btw.1.mem_affineSpan

#print axioms openSegment_subset_firstPetal_of_coreEdge
#print axioms endpointBoundary_openSegment_hitsCore
#print axioms endpointBoundary_baseLine_hitsCore

end FanoLowerBound
