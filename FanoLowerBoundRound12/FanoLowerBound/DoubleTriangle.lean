import FanoLowerBound.BoundaryExit

/-!
# Double-triangle inclusion in the sunflower line-core proof

The original proof of the three-petal line-core lemma uses two open triangles.
Rather than introducing relative-interior machinery, we isolate exactly the
swept region used by the proof: points strictly between a vertex `p` and a
point strictly between the edge endpoints `c,q`.

If the open edge `(c,q)` lies in a convex set `W` and `p ∈ W`, then this swept
triangle region lies in `W`. Applying the same argument to two petals gives
the two triangle inclusions required before the parallel-line step.
-/

namespace FanoLowerBound

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The open swept triangle with apex `p` and open opposite edge `(c,q)`.
For affinely independent `p,c,q`, this is the relative interior of their
triangle. This swept definition is the exact form used in the line-core
argument and remains meaningful without a nondegeneracy assumption. -/
def SweptTriangleInterior (p c q : E) : Set E :=
  {x | ∃ y : E, Sbtw ℝ c y q ∧ Sbtw ℝ p x y}

/-- If the open edge `(c,q)` lies in a convex set and the apex lies in that
set, then the whole swept triangle interior lies in the set. -/
theorem sweptTriangleInterior_subset_of_openEdge
    {W : Set E} (hW : Convex ℝ W)
    {p c q : E} (hp : p ∈ W)
    (hedge : ∀ y : E, Sbtw ℝ c y q → y ∈ W) :
    SweptTriangleInterior p c q ⊆ W := by
  intro x hx
  rcases hx with ⟨y, hyedge, hpxy⟩
  exact hW.mem_of_wbtw hpxy.wbtw hp (hedge y hyedge)

/-- The two triangle inclusions used in the sunflower line-core proof. The
open edge `(c,q)` is assumed to lie in a common core `C`, and `C` is contained
in both petals. -/
theorem doubleSweptTriangleInterior_subset_petals
    {C W₁ W₃ : Set E}
    (hW₁ : Convex ℝ W₁) (hW₃ : Convex ℝ W₃)
    (hCW₁ : C ⊆ W₁) (hCW₃ : C ⊆ W₃)
    {p₁ p₃ c q : E} (hp₁ : p₁ ∈ W₁) (hp₃ : p₃ ∈ W₃)
    (hedge : ∀ y : E, Sbtw ℝ c y q → y ∈ C) :
    SweptTriangleInterior p₁ c q ⊆ W₁ ∧
      SweptTriangleInterior p₃ c q ⊆ W₃ := by
  constructor
  · exact sweptTriangleInterior_subset_of_openEdge hW₁ hp₁
      (fun y hy => hCW₁ (hedge y hy))
  · exact sweptTriangleInterior_subset_of_openEdge hW₃ hp₃
      (fun y hy => hCW₃ (hedge y hy))

/-- Boundary selection plus both triangle inclusions in one statement. This
is the exact interface needed for the next parallel-line stage of the
line-core proof. -/
theorem exists_boundaryPoint_with_doubleTriangleInclusions
    {C W₁ W₃ : Set E}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hC : IsOpen C)
    (hW₁ : Convex ℝ W₁) (hW₃ : Convex ℝ W₃)
    (hCW₁ : C ⊆ W₁) (hCW₃ : C ⊆ W₃)
    {p p₁ p₃ c : E}
    (hp : p ∉ C) (hc : c ∈ C)
    (hp₁ : p₁ ∈ W₁) (hp₃ : p₃ ∈ W₃) :
    ∃ q : E,
      q ∉ C ∧
      Wbtw ℝ c q p ∧
      SweptTriangleInterior p₁ c q ⊆ W₁ ∧
      SweptTriangleInterior p₃ c q ⊆ W₃ := by
  obtain ⟨q, hq, hcqp, hedge⟩ :=
    exists_boundaryPoint_between_inside_outside hC hp hc
  obtain ⟨htri₁, htri₃⟩ :=
    doubleSweptTriangleInterior_subset_petals
      hW₁ hW₃ hCW₁ hCW₃ hp₁ hp₃ hedge
  exact ⟨q, hq, hcqp, htri₁, htri₃⟩

#print axioms sweptTriangleInterior_subset_of_openEdge
#print axioms doubleSweptTriangleInterior_subset_petals
#print axioms exists_boundaryPoint_with_doubleTriangleInclusions

end FanoLowerBound
