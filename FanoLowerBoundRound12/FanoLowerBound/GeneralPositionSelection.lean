import FanoLowerBound.SixChosenFanoLines
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# General-position representatives from six nonempty open subsets of `ℝ³`

This module proves the remaining selection lemma in the published three-dimensional
lower-bound argument for the Fano-plane neural code.  From six nonempty open sets in
`Point3 = Fin 3 → ℝ`, it selects one point in each set so that every four selected
points are affinely independent.

The proof is constructive at the finite-combinatorial level.  Points are chosen
sequentially while avoiding the affine spans of all old triples.  A finite list of
proper affine subspaces cannot cover a nonempty open set because successive set
differences remain open and the affine span of a nonempty open set is the whole
ambient space.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FanoLowerBound

open Set

/-- Affine span of one point. -/
def span1 (a : Point3) : AffineSubspace ℝ Point3 :=
  affineSpan ℝ ({a} : Set Point3)

/-- Affine span of two points. -/
def span2 (a b : Point3) : AffineSubspace ℝ Point3 :=
  affineSpan ℝ ({a, b} : Set Point3)

/-- Affine span of three points. -/
def span3 (a b c : Point3) : AffineSubspace ℝ Point3 :=
  affineSpan ℝ ({a, b, c} : Set Point3)

/-- A nonempty open set contains a point outside every fixed proper affine subspace. -/
theorem IsOpen.exists_mem_not_mem_proper_affineSubspace
    {A : Set Point3} (hA : IsOpen A) (hne : A.Nonempty)
    (S : AffineSubspace ℝ Point3) (hS : S ≠ ⊤) :
    ∃ x : Point3, x ∈ A ∧ x ∉ S := by
  by_contra h
  push_neg at h
  have hsub : A ⊆ (S : Set Point3) := fun x hx => h x hx
  have hle : affineSpan ℝ A ≤ S := affineSpan_le.2 hsub
  have htop : affineSpan ℝ A = ⊤ := hA.affineSpan_eq_top hne
  rw [htop] at hle
  exact hS (top_unique hle)

/-- A nonempty open set contains a point avoiding any finite list of proper affine subspaces. -/
theorem IsOpen.exists_mem_avoid_affineSubspaces
    {A : Set Point3} (hA : IsOpen A) (hne : A.Nonempty)
    (L : List (AffineSubspace ℝ Point3))
    (hproper : ∀ S ∈ L, S ≠ ⊤) :
    ∃ x : Point3, x ∈ A ∧ ∀ S ∈ L, x ∉ S := by
  induction L generalizing A with
  | nil =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
  | cons S L ih =>
      have hS : S ≠ ⊤ := hproper S (by simp)
      obtain ⟨y, hyA, hyS⟩ :=
        hA.exists_mem_not_mem_proper_affineSubspace hne S hS
      have hopen' : IsOpen (A \ (S : Set Point3)) :=
        hA.sdiff S.closed_of_finiteDimensional
      have hne' : (A \ (S : Set Point3)).Nonempty := ⟨y, hyA, hyS⟩
      have hproper' : ∀ T ∈ L, T ≠ ⊤ := by
        intro T hT
        exact hproper T (by simp [hT])
      obtain ⟨x, hx, havoid⟩ := ih hopen' hne' hproper'
      refine ⟨x, hx.1, ?_⟩
      intro T hT
      rcases List.mem_cons.mp hT with rfl | hTL
      · exact hx.2
      · exact havoid T hTL

/-- The affine span of one point is proper in `ℝ³`. -/
theorem span1_ne_top (a : Point3) : span1 a ≠ ⊤ := by
  intro htop
  have hind : AffineIndependent ℝ (![a] : Fin 1 → Point3) :=
    affineIndependent_of_subsingleton ℝ _
  have hcard :=
    (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).1 (by
      simpa [span1] using htop)
  norm_num [Point3] at hcard

/-- The affine span of two distinct points is proper in `ℝ³`. -/
theorem span2_ne_top {a b : Point3} (hab : a ≠ b) : span2 a b ≠ ⊤ := by
  intro htop
  have hind : AffineIndependent ℝ (![a, b] : Fin 2 → Point3) :=
    affineIndependent_of_ne ℝ hab
  have hcard :=
    (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).1 (by
      simpa [span2] using htop)
  norm_num [Point3] at hcard

/-- The affine span of three affinely independent points is proper in `ℝ³`. -/
theorem span3_ne_top {a b c : Point3}
    (habc : AffineIndependent ℝ (![a, b, c] : Fin 3 → Point3)) :
    span3 a b c ≠ ⊤ := by
  intro htop
  have hcard :=
    (habc.affineSpan_eq_top_iff_card_eq_finrank_add_one).1 (by
      simpa [span3] using htop)
  norm_num [Point3] at hcard

/-- Appending a point outside the affine span of an independent triple gives an independent quadruple. -/
theorem affineIndependent_fin4_of_fin3_of_notMem_span
    {a b c d : Point3}
    (habc : AffineIndependent ℝ (![a, b, c] : Fin 3 → Point3))
    (hd : d ∉ span3 a b c) :
    AffineIndependent ℝ (![a, b, c, d] : Fin 4 → Point3) := by
  let f : Fin 4 → Point3 := ![a, b, c, d]
  have hsub : AffineIndependent ℝ (fun x : {y : Fin 4 // y ≠ 3} => f x) := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (3 : Fin 4))]
    convert habc using 1
    ext i
    fin_cases i <;> rfl
  apply hsub.affineIndependent_of_notMem_span
  intro hmem
  apply hd
  have himage : f '' {x : Fin 4 | x ≠ 3} = ({a, b, c} : Set Point3) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all [f]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  rwa [himage] at hmem

/-- The four triples obtained by deleting one entry from an independent quadruple. -/
theorem affineIndependent_triples_of_fin4
    {a b c d : Point3}
    (h : AffineIndependent ℝ (![a, b, c, d] : Fin 4 → Point3)) :
    AffineIndependent ℝ (![a, b, c] : Fin 3 → Point3) ∧
    AffineIndependent ℝ (![a, b, d] : Fin 3 → Point3) ∧
    AffineIndependent ℝ (![a, c, d] : Fin 3 → Point3) ∧
    AffineIndependent ℝ (![b, c, d] : Fin 3 → Point3) := by
  constructor
  · let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 2], by decide⟩
    simpa [e, Function.comp_def] using h.comp_embedding e
  constructor
  · let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide⟩
    simpa [e, Function.comp_def] using h.comp_embedding e
  constructor
  · let e : Fin 3 ↪ Fin 4 := ⟨![0, 2, 3], by decide⟩
    simpa [e, Function.comp_def] using h.comp_embedding e
  · let e : Fin 3 ↪ Fin 4 := ⟨![1, 2, 3], by decide⟩
    simpa [e, Function.comp_def] using h.comp_embedding e

/-- Canonical increasing embeddings of four indices into six. -/
def quad0123 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 3], by decide⟩
def quad0124 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 4], by decide⟩
def quad0125 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 5], by decide⟩
def quad0134 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 3, 4], by decide⟩
def quad0135 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 3, 5], by decide⟩
def quad0145 : Fin 4 ↪ Fin 6 := ⟨![0, 1, 4, 5], by decide⟩
def quad0234 : Fin 4 ↪ Fin 6 := ⟨![0, 2, 3, 4], by decide⟩
def quad0235 : Fin 4 ↪ Fin 6 := ⟨![0, 2, 3, 5], by decide⟩
def quad0245 : Fin 4 ↪ Fin 6 := ⟨![0, 2, 4, 5], by decide⟩
def quad0345 : Fin 4 ↪ Fin 6 := ⟨![0, 3, 4, 5], by decide⟩
def quad1234 : Fin 4 ↪ Fin 6 := ⟨![1, 2, 3, 4], by decide⟩
def quad1235 : Fin 4 ↪ Fin 6 := ⟨![1, 2, 3, 5], by decide⟩
def quad1245 : Fin 4 ↪ Fin 6 := ⟨![1, 2, 4, 5], by decide⟩
def quad1345 : Fin 4 ↪ Fin 6 := ⟨![1, 3, 4, 5], by decide⟩
def quad2345 : Fin 4 ↪ Fin 6 := ⟨![2, 3, 4, 5], by decide⟩

/-- Every embedding `Fin 4 ↪ Fin 6` is a permutation of exactly one increasing canonical embedding. -/
theorem every_fin4_emb_fin6_factors :
    ∀ e : Fin 4 ↪ Fin 6,
      (∃ σ : Equiv.Perm (Fin 4), e = quad0123.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0124.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0125.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0134.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0135.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0145.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0234.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0235.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0245.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad0345.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad1234.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad1235.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad1245.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad1345.comp σ.toEmbedding) ∨
      (∃ σ : Equiv.Perm (Fin 4), e = quad2345.comp σ.toEmbedding) := by
  decide

/-- Six nonempty open subsets of `ℝ³` have representatives in four-wise affine general position. -/
theorem exists_six_generalPosition_representatives
    (A : Fin 6 → Set Point3)
    (hopen : ∀ i, IsOpen (A i))
    (hnonempty : ∀ i, (A i).Nonempty) :
    ∃ p : Fin 6 → Point3,
      (∀ i, p i ∈ A i) ∧
      (∀ e : Fin 4 ↪ Fin 6, AffineIndependent ℝ (p ∘ e)) := by
  obtain ⟨p0, hp0⟩ := hnonempty 0

  obtain ⟨p1, hp1A, hp1span⟩ :=
    (hopen 1).exists_mem_not_mem_proper_affineSubspace
      (hnonempty 1) (span1 p0) (span1_ne_top p0)
  have hp01ne : p0 ≠ p1 := by
    intro h
    subst p1
    apply hp1span
    exact mem_affineSpan ℝ (by simp)
  have h01 : AffineIndependent ℝ (![p0, p1] : Fin 2 → Point3) :=
    affineIndependent_of_ne ℝ hp01ne

  obtain ⟨p2, hp2A, hp2span⟩ :=
    (hopen 2).exists_mem_not_mem_proper_affineSubspace
      (hnonempty 2) (span2 p0 p1) (span2_ne_top hp01ne)
  have h012 : AffineIndependent ℝ (![p0, p1, p2] : Fin 3 → Point3) := by
    apply affineIndependent_of_ne_of_mem_of_mem_of_notMem (k := ℝ)
      (s := span2 p0 p1) hp01ne
    · exact mem_affineSpan ℝ (by simp [span2])
    · exact mem_affineSpan ℝ (by simp [span2])
    · exact hp2span

  obtain ⟨p3, hp3A, hp3span⟩ :=
    (hopen 3).exists_mem_not_mem_proper_affineSubspace
      (hnonempty 3) (span3 p0 p1 p2) (span3_ne_top h012)
  have h0123 : AffineIndependent ℝ (![p0, p1, p2, p3] : Fin 4 → Point3) :=
    affineIndependent_fin4_of_fin3_of_notMem_span h012 hp3span
  obtain ⟨h012', h013, h023, h123⟩ := affineIndependent_triples_of_fin4 h0123

  let L4 : List (AffineSubspace ℝ Point3) :=
    [span3 p0 p1 p2, span3 p0 p1 p3, span3 p0 p2 p3, span3 p1 p2 p3]
  have hL4proper : ∀ S ∈ L4, S ≠ ⊤ := by
    intro S hS
    simp only [L4, List.mem_cons, List.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl
    · exact span3_ne_top h012'
    · exact span3_ne_top h013
    · exact span3_ne_top h023
    · exact span3_ne_top h123
  obtain ⟨p4, hp4A, hp4avoid⟩ :=
    (hopen 4).exists_mem_avoid_affineSubspaces (hnonempty 4) L4 hL4proper
  have hp4_012 : p4 ∉ span3 p0 p1 p2 := hp4avoid _ (by simp [L4])
  have hp4_013 : p4 ∉ span3 p0 p1 p3 := hp4avoid _ (by simp [L4])
  have hp4_023 : p4 ∉ span3 p0 p2 p3 := hp4avoid _ (by simp [L4])
  have hp4_123 : p4 ∉ span3 p1 p2 p3 := hp4avoid _ (by simp [L4])
  have h0124 := affineIndependent_fin4_of_fin3_of_notMem_span h012' hp4_012
  have h0134 := affineIndependent_fin4_of_fin3_of_notMem_span h013 hp4_013
  have h0234 := affineIndependent_fin4_of_fin3_of_notMem_span h023 hp4_023
  have h1234 := affineIndependent_fin4_of_fin3_of_notMem_span h123 hp4_123

  obtain ⟨_, h014, h024, h124⟩ := affineIndependent_triples_of_fin4 h0124
  obtain ⟨_, _, h034, h134⟩ := affineIndependent_triples_of_fin4 h0134
  obtain ⟨_, _, _, h234⟩ := affineIndependent_triples_of_fin4 h0234

  let L5 : List (AffineSubspace ℝ Point3) :=
    [ span3 p0 p1 p2, span3 p0 p1 p3, span3 p0 p1 p4,
      span3 p0 p2 p3, span3 p0 p2 p4, span3 p0 p3 p4,
      span3 p1 p2 p3, span3 p1 p2 p4, span3 p1 p3 p4,
      span3 p2 p3 p4 ]
  have hL5proper : ∀ S ∈ L5, S ≠ ⊤ := by
    intro S hS
    simp only [L5, List.mem_cons, List.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact span3_ne_top h012'
    · exact span3_ne_top h013
    · exact span3_ne_top h014
    · exact span3_ne_top h023
    · exact span3_ne_top h024
    · exact span3_ne_top h034
    · exact span3_ne_top h123
    · exact span3_ne_top h124
    · exact span3_ne_top h134
    · exact span3_ne_top h234
  obtain ⟨p5, hp5A, hp5avoid⟩ :=
    (hopen 5).exists_mem_avoid_affineSubspaces (hnonempty 5) L5 hL5proper

  have h0125 := affineIndependent_fin4_of_fin3_of_notMem_span h012'
    (hp5avoid _ (by simp [L5]))
  have h0135 := affineIndependent_fin4_of_fin3_of_notMem_span h013
    (hp5avoid _ (by simp [L5]))
  have h0145 := affineIndependent_fin4_of_fin3_of_notMem_span h014
    (hp5avoid _ (by simp [L5]))
  have h0235 := affineIndependent_fin4_of_fin3_of_notMem_span h023
    (hp5avoid _ (by simp [L5]))
  have h0245 := affineIndependent_fin4_of_fin3_of_notMem_span h024
    (hp5avoid _ (by simp [L5]))
  have h0345 := affineIndependent_fin4_of_fin3_of_notMem_span h034
    (hp5avoid _ (by simp [L5]))
  have h1235 := affineIndependent_fin4_of_fin3_of_notMem_span h123
    (hp5avoid _ (by simp [L5]))
  have h1245 := affineIndependent_fin4_of_fin3_of_notMem_span h124
    (hp5avoid _ (by simp [L5]))
  have h1345 := affineIndependent_fin4_of_fin3_of_notMem_span h134
    (hp5avoid _ (by simp [L5]))
  have h2345 := affineIndependent_fin4_of_fin3_of_notMem_span h234
    (hp5avoid _ (by simp [L5]))

  let p : Fin 6 → Point3 := ![p0, p1, p2, p3, p4, p5]
  refine ⟨p, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hp0
    · exact hp1A
    · exact hp2A
    · exact hp3A
    · exact hp4A
    · exact hp5A
  · intro e
    rcases every_fin4_emb_fin6_factors e with
      ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ |
      ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ |
      ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩ | ⟨σ, rfl⟩
    · simpa [p, quad0123, Function.comp_def] using h0123.comp_embedding σ.toEmbedding
    · simpa [p, quad0124, Function.comp_def] using h0124.comp_embedding σ.toEmbedding
    · simpa [p, quad0125, Function.comp_def] using h0125.comp_embedding σ.toEmbedding
    · simpa [p, quad0134, Function.comp_def] using h0134.comp_embedding σ.toEmbedding
    · simpa [p, quad0135, Function.comp_def] using h0135.comp_embedding σ.toEmbedding
    · simpa [p, quad0145, Function.comp_def] using h0145.comp_embedding σ.toEmbedding
    · simpa [p, quad0234, Function.comp_def] using h0234.comp_embedding σ.toEmbedding
    · simpa [p, quad0235, Function.comp_def] using h0235.comp_embedding σ.toEmbedding
    · simpa [p, quad0245, Function.comp_def] using h0245.comp_embedding σ.toEmbedding
    · simpa [p, quad0345, Function.comp_def] using h0345.comp_embedding σ.toEmbedding
    · simpa [p, quad1234, Function.comp_def] using h1234.comp_embedding σ.toEmbedding
    · simpa [p, quad1235, Function.comp_def] using h1235.comp_embedding σ.toEmbedding
    · simpa [p, quad1245, Function.comp_def] using h1245.comp_embedding σ.toEmbedding
    · simpa [p, quad1345, Function.comp_def] using h1345.comp_embedding σ.toEmbedding
    · simpa [p, quad2345, Function.comp_def] using h2345.comp_embedding σ.toEmbedding

#print axioms IsOpen.exists_mem_not_mem_proper_affineSubspace
#print axioms IsOpen.exists_mem_avoid_affineSubspaces
#print axioms every_fin4_emb_fin6_factors
#print axioms exists_six_generalPosition_representatives

end FanoLowerBound
