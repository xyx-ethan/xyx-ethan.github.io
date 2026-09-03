import FanoLowerBound.EndpointBranch

/-!
# Ordered open-convex sunflower line-core theorem

This module combines the strict-boundary parallel-crossing branch with the
endpoint branch.  For three ordered collinear petal points, an open convex
three-sunflower with nonempty core must meet the original line in its core.
-/

namespace FanoLowerBound

open AffineMap Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- An open neighborhood of `q` contains a symmetric pair
`q ± ε v` for some `0 < ε < ε₀`. -/
theorem exists_small_symmetric_points_mem_open
    {U : Set E} (hU : IsOpen U) {q v : E} (hq : q ∈ U)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, ε ∈ Ioo (0 : ℝ) ε₀ ∧
      q - ε • v ∈ U ∧ q + ε • v ∈ U := by
  let fminus : ℝ → E := fun ε => q - ε • v
  let fplus : ℝ → E := fun ε => q + ε • v
  have hsmul : Continuous (fun ε : ℝ => ε • v) :=
    continuous_id.smul continuous_const
  have hfminus : Continuous fminus := by
    dsimp [fminus]
    exact continuous_const.sub hsmul
  have hfplus : Continuous fplus := by
    dsimp [fplus]
    exact continuous_const.add hsmul
  let N : Set ℝ := fminus ⁻¹' U ∩ fplus ⁻¹' U
  have hNopen : IsOpen N := by
    dsimp [N]
    exact (hU.preimage hfminus).inter (hU.preimage hfplus)
  have h0N : (0 : ℝ) ∈ N := by
    constructor <;> simpa [N, fminus, fplus] using hq
  have h0cl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) ε₀) := by
    rw [closure_Ioo (ne_of_lt hε₀)]
    exact ⟨le_rfl, hε₀.le⟩
  have hmeet : (N ∩ Ioo (0 : ℝ) ε₀).Nonempty :=
    mem_closure_iff_nhds.mp h0cl N (hNopen.mem_nhds h0N)
  rcases hmeet with ⟨ε, hεN, hε⟩
  exact ⟨ε, hε, hεN.1, hεN.2⟩

/-- Ordered form of the open-convex sunflower line-core theorem.  The three
chosen petal points lie on one line with the second strictly between the first
and third.  Then the line contains a common-core point. -/
theorem ordered_openConvexThreeSunflower_line_hitsCore
    {U₁ U₂ U₃ : Set E}
    (hU₁open : IsOpen U₁) (hU₂open : IsOpen U₂) (hU₃open : IsOpen U₃)
    (hU₁conv : Convex ℝ U₁) (hU₂conv : Convex ℝ U₂) (hU₃conv : Convex ℝ U₃)
    (hsun : IsThreeSunflower U₁ U₂ U₃)
    (hcore : ∃ c : E, InThreeCore U₁ U₂ U₃ c)
    {p₁ p₂ p₃ : E}
    (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hp₃ : p₃ ∈ U₃)
    (hp₂btw : Sbtw ℝ p₁ p₂ p₃) :
    ∃ z : E, InThreeCore U₁ U₂ U₃ z ∧ z ∈ line[ℝ, p₁, p₃] := by
  by_cases hp₂core : InThreeCore U₁ U₂ U₃ p₂
  · exact ⟨p₂, hp₂core, hp₂btw.1.mem_affineSpan⟩
  obtain ⟨c, hc⟩ := hcore
  by_cases hcline : c ∈ line[ℝ, p₁, p₃]
  · exact ⟨c, hc, hcline⟩
  let C : Set E := (U₁ ∩ U₂) ∩ U₃
  have hCopen : IsOpen C := by
    dsimp [C]
    exact (hU₁open.inter hU₂open).inter hU₃open
  have hcC : c ∈ C := ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩
  have hp₂notC : p₂ ∉ C := by
    intro hp₂C
    exact hp₂core ⟨hp₂C.1.1, hp₂C.1.2, hp₂C.2⟩
  obtain ⟨q, hqnotC, hqbtw, hedgeC⟩ :=
    exists_boundaryPoint_between_inside_outside hCopen hp₂notC hcC
  have hqnotcore : ¬ InThreeCore U₁ U₂ U₃ q := by
    intro hqcore
    exact hqnotC ⟨⟨hqcore.1, hqcore.2.1⟩, hqcore.2.2⟩
  have hedgeCore : ∀ y : E, Sbtw ℝ c y q → InThreeCore U₁ U₂ U₃ y := by
    intro y hy
    have hyC := hedgeC y hy
    exact ⟨hyC.1.1, hyC.1.2, hyC.2⟩
  have hcq : c ≠ q := by
    intro h
    apply hqnotcore
    simpa [h] using hc
  rcases weakBoundary_endpoint_or_strict hcq hqbtw with hqeq | hqstrict
  · subst q
    exact endpointBoundary_baseLine_hitsCore
      hU₁open hU₂open hU₁conv hsun hp₂btw hp₁ hp₂ hc hp₂core hedgeCore
  · have hqU₂ : q ∈ U₂ := hU₂conv.mem_of_wbtw hqstrict.1 hc.2.1 hp₂
    have htri₁ : SweptTriangleInterior p₁ c q ⊆ U₁ :=
      sweptTriangleInterior_subset_of_openEdge hU₁conv hp₁
        (fun y hy => (hedgeCore y hy).1)
    have htri₃ : SweptTriangleInterior p₃ c q ⊆ U₃ :=
      sweptTriangleInterior_subset_of_openEdge hU₃conv hp₃
        (fun y hy => (hedgeCore y hy).2.2)
    obtain ⟨ε₀, hε₀, hcross⟩ :=
      parallelLine_crosses_doubleSweptTriangles hp₂btw hqstrict hcline
    obtain ⟨ε, hε, hminusU₂, hplusU₂⟩ :=
      exists_small_symmetric_points_mem_open (v := p₃ - p₁) hU₂open hqU₂ hε₀
    have hcrossε := hcross ε hε.1 hε.2
    let v : E := p₃ - p₁
    let xminus : E := q - ε • v
    let xplus : E := q + ε • v
    have hxminusU₁ : xminus ∈ U₁ := by
      dsimp [xminus, v]
      exact htri₁ hcrossε.1
    have hxminusU₂ : xminus ∈ U₂ := by
      dsimp [xminus, v]
      exact hminusU₂
    have hxminusU₃ : xminus ∈ U₃ := hsun.1 ⟨hxminusU₁, hxminusU₂⟩
    have hxplusU₃ : xplus ∈ U₃ := by
      dsimp [xplus, v]
      exact htri₃ hcrossε.2
    have hxplusU₂ : xplus ∈ U₂ := by
      dsimp [xplus, v]
      exact hplusU₂
    have hxplusU₁ : xplus ∈ U₁ := hsun.2.2 ⟨hxplusU₂, hxplusU₃⟩
    have hqmid : Wbtw ℝ xminus q xplus := by
      refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
      dsimp [xminus, xplus, v]
      rw [lineMap_apply_module]
      module
    have hqU₁ : q ∈ U₁ := hU₁conv.mem_of_wbtw hqmid hxminusU₁ hxplusU₁
    have hqU₃ : q ∈ U₃ := hU₃conv.mem_of_wbtw hqmid hxminusU₃ hxplusU₃
    exact (hqnotcore ⟨hqU₁, hqU₂, hqU₃⟩).elim

#print axioms exists_small_symmetric_points_mem_open
#print axioms ordered_openConvexThreeSunflower_line_hitsCore

end FanoLowerBound
