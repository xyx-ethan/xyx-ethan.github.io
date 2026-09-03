import FanoLowerBound.SixPointRadonComplete
import Mathlib.Analysis.Convex.Between

/-!
# Sunflower line and segment lemmas

This module isolates the order-convex part of the open-convex sunflower
argument used in Lemma 7 of `Embedding dimension gaps in sparse codes`.

The genuinely topological input of the preceding line-core lemma is represented
by `EveryLineMeetingThreeHitsCore`.  From that input, convexity and the
sunflower equal-pairwise-intersection property force every third-petal point on
the segment joining the first two petals into the common core.
-/

namespace FanoLowerBound

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For three sets, every pairwise intersection is contained in the third set.
Equivalently, all three pairwise intersections equal the triple intersection. -/
def IsThreeSunflower (U₁ U₂ U₃ : Set E) : Prop :=
  U₁ ∩ U₂ ⊆ U₃ ∧ U₁ ∩ U₃ ⊆ U₂ ∧ U₂ ∩ U₃ ⊆ U₁

/-- Membership in the common core of three sets. -/
def InThreeCore (U₁ U₂ U₃ : Set E) (x : E) : Prop :=
  x ∈ U₁ ∧ x ∈ U₂ ∧ x ∈ U₃

/-- The line-transversal conclusion supplied by the open-convex sunflower
line-core theorem: every affine line meeting all three petals meets the core. -/
def EveryLineMeetingThreeHitsCore (U₁ U₂ U₃ : Set E) : Prop :=
  ∀ p q : E,
    (∃ x, x ∈ U₁ ∧ x ∈ line[ℝ, p, q]) →
    (∃ x, x ∈ U₂ ∧ x ∈ line[ℝ, p, q]) →
    (∃ x, x ∈ U₃ ∧ x ∈ line[ℝ, p, q]) →
    ∃ c, InThreeCore U₁ U₂ U₃ c ∧ c ∈ line[ℝ, p, q]

/-- A core point anywhere on the affine line through `p₁,p₂` can be replaced
by a core point on the closed segment.  If its line parameter is outside
`[0,1]`, convexity and the sunflower property force the nearer endpoint into
the core. -/
theorem corePoint_on_segment_of_corePoint_on_line
    {U₁ U₂ U₃ : Set E}
    (hU₁ : Convex ℝ U₁) (hU₂ : Convex ℝ U₂)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    {p₁ p₂ c : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂)
    (hc : InThreeCore U₁ U₂ U₃ c)
    (hcline : c ∈ line[ℝ, p₁, p₂]) :
    ∃ c', InThreeCore U₁ U₂ U₃ c' ∧ c' ∈ segment ℝ p₁ p₂ := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hcline
  rcases hcline with ⟨r, rfl⟩
  by_cases hr0 : r < 0
  · have hw : Wbtw ℝ (AffineMap.lineMap p₁ p₂ r) p₁ p₂ := by
      simpa using (Wbtw.of_le_of_le hr0.le zero_le_one).map (AffineMap.lineMap p₁ p₂)
    have hp₁U₂ : p₁ ∈ U₂ := hU₂.mem_of_wbtw hw hc.2.1 hp₂
    have hp₁U₃ : p₁ ∈ U₃ := hsun.1 ⟨hp₁, hp₁U₂⟩
    exact ⟨p₁, ⟨hp₁, hp₁U₂, hp₁U₃⟩, left_mem_segment ℝ p₁ p₂⟩
  · have hr0' : 0 ≤ r := le_of_not_gt hr0
    by_cases hr1 : r ≤ 1
    · have hw : Wbtw ℝ p₁ (AffineMap.lineMap p₁ p₂ r) p₂ := by
        simpa using (Wbtw.of_le_of_le hr0' hr1).map (AffineMap.lineMap p₁ p₂)
      exact ⟨AffineMap.lineMap p₁ p₂ r, hc, hw.mem_segment⟩
    · have hr1' : 1 < r := lt_of_not_ge hr1
      have hw : Wbtw ℝ p₁ p₂ (AffineMap.lineMap p₁ p₂ r) := by
        simpa using (Wbtw.of_le_of_le zero_le_one hr1'.le).map (AffineMap.lineMap p₁ p₂)
      have hp₂U₁ : p₂ ∈ U₁ := hU₁.mem_of_wbtw hw hp₁ hc.1
      have hp₂U₃ : p₂ ∈ U₃ := hsun.1 ⟨hp₂U₁, hp₂⟩
      exact ⟨p₂, ⟨hp₂U₁, hp₂, hp₂U₃⟩, right_mem_segment ℝ p₁ p₂⟩

/-- Two points on the same segment are ordered by their line parameters.  A
core point on `p₁p₂`, together with a third-petal point on the same segment,
forces the latter into the core by convexity and the sunflower property. -/
theorem sunflower_segment_of_corePoint_on_segment
    {U₁ U₂ U₃ : Set E}
    (hU₁ : Convex ℝ U₁) (hU₂ : Convex ℝ U₂)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    {p₁ p₂ p₃ c : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hp₃ : p₃ ∈ U₃)
    (hc : InThreeCore U₁ U₂ U₃ c)
    (hcseg : c ∈ segment ℝ p₁ p₂)
    (hp₃seg : p₃ ∈ segment ℝ p₁ p₂) :
    InThreeCore U₁ U₂ U₃ p₃ := by
  have hcw : Wbtw ℝ p₁ c p₂ := (mem_segment_iff_wbtw).1 hcseg
  have hpw : Wbtw ℝ p₁ p₃ p₂ := (mem_segment_iff_wbtw).1 hp₃seg
  rcases hcw with ⟨t, ht, htc⟩
  rcases hpw with ⟨s, hs, hsp⟩
  have hc_eq : AffineMap.lineMap p₁ p₂ t = c := htc
  have hp_eq : AffineMap.lineMap p₁ p₂ s = p₃ := hsp
  rcases le_total s t with hst | hts
  · have hw0 : Wbtw ℝ (0 : ℝ) s t := Wbtw.of_le_of_le hs.1 hst
    have hw : Wbtw ℝ p₁ p₃ c := by
      simpa [hc_eq, hp_eq] using hw0.map (AffineMap.lineMap p₁ p₂)
    have hp₃U₁ : p₃ ∈ U₁ := hU₁.mem_of_wbtw hw hp₁ hc.1
    have hp₃U₂ : p₃ ∈ U₂ := hsun.2.1 ⟨hp₃U₁, hp₃⟩
    exact ⟨hp₃U₁, hp₃U₂, hp₃⟩
  · have hw0 : Wbtw ℝ t s 1 := Wbtw.of_le_of_le hts hs.2
    have hw : Wbtw ℝ c p₃ p₂ := by
      simpa [hc_eq, hp_eq] using hw0.map (AffineMap.lineMap p₁ p₂)
    have hp₃U₂ : p₃ ∈ U₂ := hU₂.mem_of_wbtw hw hc.2.1 hp₂
    have hp₃U₁ : p₃ ∈ U₁ := hsun.2.2 ⟨hp₃U₂, hp₃⟩
    exact ⟨hp₃U₁, hp₃U₂, hp₃⟩

/-- Lemma 7 with the line-core conclusion supplied explicitly.  The core point
may initially lie anywhere on the affine line, not necessarily on the joining
segment. -/
theorem sunflower_segment_of_line_hits_core
    {U₁ U₂ U₃ : Set E}
    (hU₁ : Convex ℝ U₁) (hU₂ : Convex ℝ U₂)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    {p₁ p₂ p₃ : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hp₃ : p₃ ∈ U₃)
    (hp₃seg : p₃ ∈ segment ℝ p₁ p₂)
    (hline : ∃ c, InThreeCore U₁ U₂ U₃ c ∧ c ∈ line[ℝ, p₁, p₂]) :
    InThreeCore U₁ U₂ U₃ p₃ := by
  rcases hline with ⟨c, hc, hcline⟩
  rcases corePoint_on_segment_of_corePoint_on_line hU₁ hU₂ hsun hp₁ hp₂ hc hcline with
    ⟨c', hc', hc'seg⟩
  exact sunflower_segment_of_corePoint_on_segment
    hU₁ hU₂ hsun hp₁ hp₂ hp₃ hc' hc'seg hp₃seg

/-- The exact order-convex deduction of the paper's Lemma 7 from the preceding
line-core property (Lemma 6). -/
theorem sunflower_segment_of_everyLineMeetingThreeHitsCore
    {U₁ U₂ U₃ : Set E}
    (hU₁ : Convex ℝ U₁) (hU₂ : Convex ℝ U₂)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    (htrans : EveryLineMeetingThreeHitsCore U₁ U₂ U₃)
    {p₁ p₂ p₃ : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hp₃ : p₃ ∈ U₃)
    (hp₃seg : p₃ ∈ segment ℝ p₁ p₂) :
    InThreeCore U₁ U₂ U₃ p₃ := by
  have hp₃line : p₃ ∈ line[ℝ, p₁, p₂] :=
    ((mem_segment_iff_wbtw).1 hp₃seg).mem_affineSpan
  have hline := htrans p₁ p₂
    ⟨p₁, hp₁, left_mem_affineSpan_pair ℝ p₁ p₂⟩
    ⟨p₂, hp₂, right_mem_affineSpan_pair ℝ p₁ p₂⟩
    ⟨p₃, hp₃, hp₃line⟩
  exact sunflower_segment_of_line_hits_core hU₁ hU₂ hsun hp₁ hp₂ hp₃ hp₃seg hline

#print axioms corePoint_on_segment_of_corePoint_on_line
#print axioms sunflower_segment_of_corePoint_on_segment
#print axioms sunflower_segment_of_line_hits_core
#print axioms sunflower_segment_of_everyLineMeetingThreeHitsCore

end FanoLowerBound
