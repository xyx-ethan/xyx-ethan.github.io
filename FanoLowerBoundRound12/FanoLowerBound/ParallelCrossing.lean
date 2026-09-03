import FanoLowerBound.DoubleTriangle
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Parallel-line crossing of the two swept triangles

This module formalizes the local affine calculation in the open-convex
sunflower line-core proof.  If `p₂` is strictly between the collinear points
`p₁,p₃`, and `q` is strictly between an off-line point `c` and `p₂`, then the
line through `q` parallel to `p₁p₃` enters the two swept triangle interiors on
opposite sides of `q`.
-/

namespace FanoLowerBound

open AffineMap Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Strictly positive barycentric coordinates in the ordered triangle
`(p,c,q)`. -/
def StrictTriangleCombination (p c q x : E) : Prop :=
  ∃ A B C : ℝ,
    0 < A ∧ 0 < B ∧ 0 < C ∧ A + B + C = 1 ∧
      x = A • p + B • c + C • q

/-- Positive barycentric coordinates give a point in the swept triangle,
provided the apex does not lie on the opposite-edge line. -/
theorem strictTriangleCombination_mem_sweptTriangleInterior
    {p c q x : E} (hcq : c ≠ q) (hp : p ∉ line[ℝ, c, q])
    (hx : StrictTriangleCombination p c q x) :
    x ∈ SweptTriangleInterior p c q := by
  rcases hx with ⟨A, B, C, hA, hB, hC, hsum, hx⟩
  let s : ℝ := B + C
  let r : ℝ := C / s
  let y : E := lineMap c q r
  have hspos : 0 < s := by
    dsimp [s]
    linarith
  have hslt : s < 1 := by
    dsimp [s]
    linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos hC hspos
  have hrlt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hspos).2 (by linarith)
  have hyedge : Sbtw ℝ c y q := by
    exact (sbtw_lineMap_iff).2 ⟨hcq, ⟨hrpos, hrlt⟩⟩
  have hpy : p ≠ y := by
    intro hpy
    apply hp
    rw [hpy]
    exact hyedge.mem_affineSpan
  have hAs : 1 - s = A := by
    dsimp [s]
    linarith
  have hsr : s * r = C := by
    dsimp [r]
    field_simp [hsne]
  have hBsr : s * (1 - r) = B := by
    calc
      s * (1 - r) = s - s * r := by ring
      _ = s - C := by rw [hsr]
      _ = B := by dsimp [s]; ring
  have hline : lineMap p y s = A • p + B • c + C • q := by
    dsimp [y]
    rw [lineMap_apply_module, lineMap_apply_module]
    simp only [smul_add, smul_smul]
    rw [hAs, hBsr, hsr]
    abel
  refine ⟨y, hyedge, ?_⟩
  rw [hx, ← hline]
  exact (sbtw_lineMap_iff).2 ⟨hpy, ⟨hspos, hslt⟩⟩

/-- Under the non-collinearity assumption on `c`, neither endpoint of the base
line lies on the opposite-edge line through `c,q`. -/
theorem base_endpoints_not_mem_edgeLine
    {p₁ p₂ p₃ c q : E}
    (hp₂ : Sbtw ℝ p₁ p₂ p₃)
    (hq : Sbtw ℝ c q p₂)
    (hc : c ∉ line[ℝ, p₁, p₃]) :
    p₁ ∉ line[ℝ, c, q] ∧ p₃ ∉ line[ℝ, c, q] := by
  constructor
  · intro hp₁cq
    have hp₂cq : p₂ ∈ line[ℝ, c, q] := hq.right_mem_affineSpan
    have h12cq : line[ℝ, p₁, p₂] = line[ℝ, c, q] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁cq hp₂cq hp₂.left_ne.symm
    have hc12 : c ∈ line[ℝ, p₁, p₂] := by
      rw [h12cq]
      exact left_mem_affineSpan_pair ℝ c q
    have h12base : line[ℝ, p₁, p₂] = line[ℝ, p₁, p₃] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ p₁ p₃) hp₂.mem_affineSpan hp₂.left_ne.symm
    apply hc
    rw [← h12base]
    exact hc12
  · intro hp₃cq
    have hp₂cq : p₂ ∈ line[ℝ, c, q] := hq.right_mem_affineSpan
    have h32cq : line[ℝ, p₃, p₂] = line[ℝ, c, q] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp₃cq hp₂cq hp₂.right_ne.symm
    have hc32 : c ∈ line[ℝ, p₃, p₂] := by
      rw [h32cq]
      exact left_mem_affineSpan_pair ℝ c q
    have h32base : line[ℝ, p₃, p₂] = line[ℝ, p₁, p₃] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (right_mem_affineSpan_pair ℝ p₁ p₃) hp₂.mem_affineSpan hp₂.right_ne.symm
    apply hc
    rw [← h32base]
    exact hc32

/-- Explicit parallel crossing with the common radius
`ε₀ = b*a*(1-a)`. -/
theorem parallel_crossing_of_lineMap_parameters
    {p₁ p₂ p₃ c q : E} {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hp₂eq : p₂ = lineMap p₁ p₃ a)
    (hqeq : q = lineMap c p₂ b)
    (hcq : c ≠ q)
    (hp₁edge : p₁ ∉ line[ℝ, c, q])
    (hp₃edge : p₃ ∉ line[ℝ, c, q]) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        q - ε • (p₃ - p₁) ∈ SweptTriangleInterior p₁ c q ∧
        q + ε • (p₃ - p₁) ∈ SweptTriangleInterior p₃ c q := by
  let ε₀ : ℝ := b * a * (1 - a)
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεlt
  have hba : 0 < b * a := mul_pos hb.1 ha.1
  have hb1a : 0 < b * (1 - a) := mul_pos hb.1 (sub_pos.2 ha.2)
  have hεba : ε < b * a := by
    dsimp [ε₀] at hεlt
    nlinarith [hb.2, ha.1, ha.2]
  have hεb1a : ε < b * (1 - a) := by
    dsimp [ε₀] at hεlt
    nlinarith [hb.1, hb.2, ha.1, ha.2]
  constructor
  · apply strictTriangleCombination_mem_sweptTriangleInterior hcq hp₁edge
    refine ⟨ε / a, (1 - b) * ε / (b * a), 1 - ε / (b * a), ?_, ?_, ?_, ?_, ?_⟩
    · exact div_pos hε ha.1
    · exact div_pos (mul_pos (sub_pos.2 hb.2) hε) hba
    · exact sub_pos.2 ((div_lt_one hba).2 hεba)
    · field_simp [ne_of_gt ha.1, ne_of_gt hb.1]
      ring
    · rw [hqeq, hp₂eq]
      simp only [lineMap_apply_module, smul_sub, smul_add, smul_smul]
      match_scalars <;> field_simp [ne_of_gt ha.1, ne_of_gt hb.1] <;> ring
  · apply strictTriangleCombination_mem_sweptTriangleInterior hcq hp₃edge
    refine ⟨ε / (1 - a), (1 - b) * ε / (b * (1 - a)),
      1 - ε / (b * (1 - a)), ?_, ?_, ?_, ?_, ?_⟩
    · exact div_pos hε (sub_pos.2 ha.2)
    · exact div_pos (mul_pos (sub_pos.2 hb.2) hε) hb1a
    · exact sub_pos.2 ((div_lt_one hb1a).2 hεb1a)
    · field_simp [ne_of_gt (sub_pos.2 ha.2), ne_of_gt hb.1]
      ring
    · rw [hqeq, hp₂eq]
      simp only [lineMap_apply_module, smul_sub, smul_add, smul_smul]
      match_scalars <;> field_simp [ne_of_gt (sub_pos.2 ha.2), ne_of_gt hb.1] <;> ring

/-- Geometric form: strict betweenness supplies `a,b`, and off-line `c`
supplies the two nondegenerate triangle conditions. -/
theorem parallelLine_crosses_doubleSweptTriangles
    {p₁ p₂ p₃ c q : E}
    (hp₂ : Sbtw ℝ p₁ p₂ p₃)
    (hq : Sbtw ℝ c q p₂)
    (hc : c ∉ line[ℝ, p₁, p₃]) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        q - ε • (p₃ - p₁) ∈ SweptTriangleInterior p₁ c q ∧
        q + ε • (p₃ - p₁) ∈ SweptTriangleInterior p₃ c q := by
  rcases ((sbtw_iff_mem_image_Ioo_and_ne).1 hp₂).1 with ⟨a, ha, haeq⟩
  rcases ((sbtw_iff_mem_image_Ioo_and_ne).1 hq).1 with ⟨b, hb, hbeq⟩
  have hedges := base_endpoints_not_mem_edgeLine hp₂ hq hc
  exact parallel_crossing_of_lineMap_parameters ha hb haeq.symm hbeq.symm
    hq.left_ne.symm hedges.1 hedges.2

/-- The weak boundary interface cannot in general be upgraded to strict
betweenness: the selected boundary point may equal the exterior endpoint. -/
theorem weakBoundary_endpoint_or_strict
    {c q p : E} (hcq : c ≠ q) (h : Wbtw ℝ c q p) :
    q = p ∨ Sbtw ℝ c q p := by
  by_cases hqp : q = p
  · exact Or.inl hqp
  · exact Or.inr ⟨h, hcq.symm, hqp⟩

#print axioms strictTriangleCombination_mem_sweptTriangleInterior
#print axioms base_endpoints_not_mem_edgeLine
#print axioms parallel_crossing_of_lineMap_parameters
#print axioms parallelLine_crosses_doubleSweptTriangles
#print axioms weakBoundary_endpoint_or_strict

end FanoLowerBound
