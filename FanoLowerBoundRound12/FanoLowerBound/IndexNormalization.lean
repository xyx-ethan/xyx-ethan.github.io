import FanoLowerBound.FanoRadonForcing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Index normalization for Fano strict Radon witnesses

An ordered strict `2--3` Radon witness may list its two-point and three-point
sides in arbitrary orders.  This file canonically sorts the two sides, proves
by finite kernel reduction that every five-distinct ordered tuple maps to one
of the 210 `RadonConfig` values, transports the Radon equality through both
permutations, and applies the Round 23 five-fold contradiction theorem.
-/

namespace FanoLowerBound

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Five ordered, labelled maximal-word indices: two on the left side of a
strict Radon equality and three on the right side. -/
structure OrderedRadonIndices where
  pair0 : Fin 7
  pair1 : Fin 7
  triple0 : Fin 7
  triple1 : Fin 7
  triple2 : Fin 7
  deriving DecidableEq, Repr, Fintype

/-- The five labels are pairwise distinct. -/
def OrderedRadonIndices.Nodup (w : OrderedRadonIndices) : Prop :=
  [w.pair0, w.pair1, w.triple0, w.triple1, w.triple2].Nodup

/-- A sorted triple of Fano maximal-word indices. -/
structure SortedTriple7 where
  first : Fin 7
  second : Fin 7
  third : Fin 7
  deriving DecidableEq, Repr

/-- A six-branch sorting network for three elements. -/
def sortTriple7 (x y z : Fin 7) : SortedTriple7 :=
  if x ≤ y then
    if y ≤ z then
      ⟨x, y, z⟩
    else if x ≤ z then
      ⟨x, z, y⟩
    else
      ⟨z, x, y⟩
  else if x ≤ z then
    ⟨y, x, z⟩
  else if y ≤ z then
    ⟨y, z, x⟩
  else
    ⟨z, y, x⟩

/-- Canonical sorting of the two-point and three-point sides. -/
def OrderedRadonIndices.canonicalConfig (w : OrderedRadonIndices) : RadonConfig :=
  let t := sortTriple7 w.triple0 w.triple1 w.triple2
  { pairA := (min w.pair0 w.pair1).val
    pairB := (max w.pair0 w.pair1).val
    triple0 := t.first.val
    triple1 := t.second.val
    triple2 := t.third.val }

/-- The output pair is a permutation of the input pair. -/
def SamePairPermutation (e0 e1 x y : Nat) : Prop :=
  (e0 = x ∧ e1 = y) ∨ (e0 = y ∧ e1 = x)

/-- Full finite specification of canonical index normalization. -/
def OrderedRadonIndices.NormalizationSpec (w : OrderedRadonIndices) : Prop :=
  w.canonicalConfig ∈ allRadonConfigs ∧
  SamePairPermutation w.canonicalConfig.pairA w.canonicalConfig.pairB
    w.pair0.val w.pair1.val ∧
  SameTriplePermutation
    w.canonicalConfig.triple0 w.canonicalConfig.triple1 w.canonicalConfig.triple2
    w.triple0.val w.triple1.val w.triple2.val

/-- Pure-kernel finite audit of all `7^5` tuples.  The implication is active on
exactly `7P5 = 2520` five-distinct tuples, which map onto the 210 canonical
configurations with `2! * 3! = 12` preimages each. -/
theorem all_orderedRadonIndices_normalize :
    ∀ w : OrderedRadonIndices, w.Nodup → w.NormalizationSpec := by
  decide

/-- Strict Radon equality is invariant under swapping its two-point side. -/
theorem StrictRadon23.swapLeft
    {x0 x1 y0 y1 y2 : E}
    (h : StrictRadon23 x0 x1 y0 y1 y2) :
    StrictRadon23 x1 x0 y0 y1 y2 := by
  rcases h with ⟨a0, a1, b0, b1, b2,
    ha0, ha1, hb0, hb1, hb2, hasum, hbsum, heq⟩
  refine ⟨a1, a0, b0, b1, b2,
    ha1, ha0, hb0, hb1, hb2, ?_, hbsum, ?_⟩
  · linarith
  · simpa [add_comm] using heq

/-- Reorder the two-point side according to a certified pair permutation. -/
theorem StrictRadon23.reorderLeft
    {P : Nat → E} {e0 e1 x y z0 z1 z2 : Nat}
    (hperm : SamePairPermutation e0 e1 x y)
    (h : StrictRadon23 (P x) (P y) (P z0) (P z1) (P z2)) :
    StrictRadon23 (P e0) (P e1) (P z0) (P z1) (P z2) := by
  rcases hperm with hxy | hyx
  · rcases hxy with ⟨rfl, rfl⟩
    exact h
  · rcases hyx with ⟨rfl, rfl⟩
    exact h.swapLeft

/-- An arbitrary ordered five-label witness is transported to its canonical
`RadonConfig`. -/
theorem OrderedRadonIndices.strictRadon_canonical
    {P : Nat → E} (w : OrderedRadonIndices)
    (hnodup : w.Nodup)
    (hrad : StrictRadon23
      (P w.pair0.val) (P w.pair1.val)
      (P w.triple0.val) (P w.triple1.val) (P w.triple2.val)) :
    StrictRadon23
      (P w.canonicalConfig.pairA) (P w.canonicalConfig.pairB)
      (P w.canonicalConfig.triple0) (P w.canonicalConfig.triple1)
      (P w.canonicalConfig.triple2) := by
  have hspec := all_orderedRadonIndices_normalize w hnodup
  have hleft : StrictRadon23
      (P w.canonicalConfig.pairA) (P w.canonicalConfig.pairB)
      (P w.triple0.val) (P w.triple1.val) (P w.triple2.val) :=
    hrad.reorderLeft hspec.2.1
  exact hleft.reorderRight hspec.2.2

/-- Any five-distinct ordered Fano strict-Radon witness contradicts the absence
of five pairwise distinct simultaneously active neurons. -/
theorem orderedRadonIndices_contradict_noFiveDistinctActive
    {U : Nat → Set E} {P : Nat → E}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : E, InThreeCore (U x) (U y) (U z) q)
    (hno5 : NoFiveDistinctActive U)
    (w : OrderedRadonIndices) (hnodup : w.Nodup)
    (hrad : StrictRadon23
      (P w.pair0.val) (P w.pair1.val)
      (P w.triple0.val) (P w.triple1.val) (P w.triple2.val)) : False := by
  have hspec := all_orderedRadonIndices_normalize w hnodup
  exact every_fano_radon_config_contradicts_noFiveDistinctActive
    hopen hconv hpoint hsun hcore hno5
    w.canonicalConfig hspec.1
    (w.strictRadon_canonical hnodup hrad)

#print axioms all_orderedRadonIndices_normalize
#print axioms StrictRadon23.swapLeft
#print axioms StrictRadon23.reorderLeft
#print axioms OrderedRadonIndices.strictRadon_canonical
#print axioms orderedRadonIndices_contradict_noFiveDistinctActive

end FanoLowerBound
