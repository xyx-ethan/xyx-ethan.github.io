import FanoLowerBound.FanoRadonForcing

/-!
# Normalizing arbitrary ordered Fano Radon indices

A strict `2--3` Radon equality may arrive with the two-point side in either
order and the three-point side in any of its six orders. This module sorts
those five pairwise distinct Fano-line labels into the canonical
`RadonConfig` convention used by the 210-record forcing table and then invokes
the semantic fivefold-intersection contradiction.
-/

namespace FanoLowerBound

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The two possible orders of the same pair of labels. -/
def SamePairPermutation (e₀ e₁ x y : Nat) : Prop :=
  (e₀ = x ∧ e₁ = y) ∨ (e₀ = y ∧ e₁ = x)

/-- Strict `2--3` Radon equality is invariant under swapping the two-point side. -/
theorem StrictRadon23.reorderLeft
    {x₀ x₁ : E} {P : Nat → E}
    {e₀ e₁ x y u v w : Nat}
    (hperm : SamePairPermutation e₀ e₁ x y)
    (h : StrictRadon23 (P x) (P y) (P u) (P v) (P w)) :
    StrictRadon23 (P e₀) (P e₁) (P u) (P v) (P w) := by
  rcases h with ⟨a₀, a₁, b₀, b₁, b₂,
    ha₀, ha₁, hb₀, hb₁, hb₂, hasum, hbsum, heq⟩
  rcases hperm with hxy | hyx
  · rcases hxy with ⟨rfl, rfl⟩
    exact ⟨a₀, a₁, b₀, b₁, b₂,
      ha₀, ha₁, hb₀, hb₁, hb₂, hasum, hbsum, heq⟩
  · rcases hyx with ⟨rfl, rfl⟩
    refine ⟨a₁, a₀, b₀, b₁, b₂,
      ha₁, ha₀, hb₀, hb₁, hb₂, ?_, hbsum, ?_⟩
    · linarith
    · simpa [add_comm] using heq

/-- A directly canonical five-label configuration belongs to the finite list
`allRadonConfigs`. -/
theorem canonicalRadonConfig_mem_allRadonConfigs
    {A B x y z : Nat}
    (hA : A < 7) (hB : B < 7)
    (hx : x < 7) (hy : y < 7) (hz : z < 7)
    (hAB : A < B) (hxy : x < y) (hyz : y < z)
    (hxA : x ≠ A) (hxB : x ≠ B)
    (hyA : y ≠ A) (hyB : y ≠ B)
    (hzA : z ≠ A) (hzB : z ≠ B) :
    ({ pairA := A, pairB := B, triple0 := x, triple1 := y, triple2 := z } :
      RadonConfig) ∈ allRadonConfigs := by
  simp only [allRadonConfigs, List.mem_flatMap]
  refine ⟨A, List.mem_range.mpr hA, B, List.mem_range.mpr hB,
    x, List.mem_range.mpr hx, y, List.mem_range.mpr hy,
    z, List.mem_range.mpr hz, ?_⟩
  have hcond : A < B ∧ x < y ∧ y < z ∧
      x ≠ A ∧ x ≠ B ∧ y ≠ A ∧ y ≠ B ∧ z ≠ A ∧ z ≠ B :=
    ⟨hAB, hxy, hyz, hxA, hxB, hyA, hyB, hzA, hzB⟩
  simp [hcond]

/-- Pair and triple permutation certificates turn an ordered strict Radon
witness into a canonical member of `allRadonConfigs`. -/
theorem canonicalized_orderedFive_hasCanonicalConfig
    {P : Nat → E}
    {A B x y z a b u v w : Nat}
    (hA : A < 7) (hB : B < 7)
    (hx : x < 7) (hy : y < 7) (hz : z < 7)
    (hAB : A < B) (hxy : x < y) (hyz : y < z)
    (hxA : x ≠ A) (hxB : x ≠ B)
    (hyA : y ≠ A) (hyB : y ≠ B)
    (hzA : z ≠ A) (hzB : z ≠ B)
    (hpair : SamePairPermutation A B a b)
    (htriple : SameTriplePermutation x y z u v w)
    (hrad : StrictRadon23 (P a) (P b) (P u) (P v) (P w)) :
    ∃ cfg ∈ allRadonConfigs,
      StrictRadon23 (P cfg.pairA) (P cfg.pairB)
        (P cfg.triple0) (P cfg.triple1) (P cfg.triple2) := by
  let cfg : RadonConfig :=
    { pairA := A, pairB := B, triple0 := x, triple1 := y, triple2 := z }
  have hcfg : cfg ∈ allRadonConfigs := by
    dsimp [cfg]
    exact canonicalRadonConfig_mem_allRadonConfigs
      hA hB hx hy hz hAB hxy hyz hxA hxB hyA hyB hzA hzB
  have hradPair : StrictRadon23 (P A) (P B) (P u) (P v) (P w) :=
    hrad.reorderLeft hpair
  have hradCanonical : StrictRadon23 (P A) (P B) (P x) (P y) (P z) :=
    hradPair.reorderRight htriple
  exact ⟨cfg, hcfg, by simpa [cfg] using hradCanonical⟩

/-- Sort the three-point side while a canonical pair order is fixed. -/
private theorem sortedPair_arbitraryTriple_hasCanonicalConfig
    {P : Nat → E}
    {A B a b u v w : Nat}
    (hA : A < 7) (hB : B < 7)
    (hu : u < 7) (hv : v < 7) (hw : w < 7)
    (hAB : A < B)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huA : u ≠ A) (huB : u ≠ B)
    (hvA : v ≠ A) (hvB : v ≠ B)
    (hwA : w ≠ A) (hwB : w ≠ B)
    (hpair : SamePairPermutation A B a b)
    (hrad : StrictRadon23 (P a) (P b) (P u) (P v) (P w)) :
    ∃ cfg ∈ allRadonConfigs,
      StrictRadon23 (P cfg.pairA) (P cfg.pairB)
        (P cfg.triple0) (P cfg.triple1) (P cfg.triple2) := by
  by_cases huvlt : u < v
  · by_cases hvwlt : v < w
    · exact canonicalized_orderedFive_hasCanonicalConfig
        hA hB hu hv hw hAB huvlt hvwlt
        huA huB hvA hvB hwA hwB hpair
        (by simp [SameTriplePermutation]) hrad
    · have hwvlt : w < v := by omega
      by_cases huwlt : u < w
      · exact canonicalized_orderedFive_hasCanonicalConfig
          hA hB hu hw hv hAB huwlt hwvlt
          huA huB hwA hwB hvA hvB hpair
          (by simp [SameTriplePermutation]) hrad
      · have hwult : w < u := by omega
        exact canonicalized_orderedFive_hasCanonicalConfig
          hA hB hw hu hv hAB hwult huvlt
          hwA hwB huA huB hvA hvB hpair
          (by simp [SameTriplePermutation]) hrad
  · have hvult : v < u := by omega
    by_cases huwlt : u < w
    · exact canonicalized_orderedFive_hasCanonicalConfig
        hA hB hv hu hw hAB hvult huwlt
        hvA hvB huA huB hwA hwB hpair
        (by simp [SameTriplePermutation]) hrad
    · have hwult : w < u := by omega
      by_cases hvwlt : v < w
      · exact canonicalized_orderedFive_hasCanonicalConfig
          hA hB hv hw hu hAB hvwlt hwult
          hvA hvB hwA hwB huA huB hpair
          (by simp [SameTriplePermutation]) hrad
      · have hwvlt : w < v := by omega
        exact canonicalized_orderedFive_hasCanonicalConfig
          hA hB hw hv hu hAB hwvlt hvult
          hwA hwB hvA hvB huA huB hpair
          (by simp [SameTriplePermutation]) hrad

/-- Any ordered strict Radon equality on five pairwise distinct labels from
`0,...,6` canonically matches one of the 210 Fano configurations. -/
theorem arbitraryOrderedFive_strictRadon_hasCanonicalConfig
    {P : Nat → E} {a b u v w : Nat}
    (ha : a < 7) (hb : b < 7)
    (hu : u < 7) (hv : v < 7) (hw : w < 7)
    (hnodup : [a, b, u, v, w].Nodup)
    (hrad : StrictRadon23 (P a) (P b) (P u) (P v) (P w)) :
    ∃ cfg ∈ allRadonConfigs,
      StrictRadon23 (P cfg.pairA) (P cfg.pairB)
        (P cfg.triple0) (P cfg.triple1) (P cfg.triple2) := by
  have hab : a ≠ b := by
    intro h
    subst b
    simpa using hnodup
  have hau : a ≠ u := by
    intro h
    subst u
    simpa using hnodup
  have hav : a ≠ v := by
    intro h
    subst v
    simpa using hnodup
  have haw : a ≠ w := by
    intro h
    subst w
    simpa using hnodup
  have hbu : b ≠ u := by
    intro h
    subst u
    simpa using hnodup
  have hbv : b ≠ v := by
    intro h
    subst v
    simpa using hnodup
  have hbw : b ≠ w := by
    intro h
    subst w
    simpa using hnodup
  have huv : u ≠ v := by
    intro h
    subst v
    simpa using hnodup
  have huw : u ≠ w := by
    intro h
    subst w
    simpa using hnodup
  have hvw : v ≠ w := by
    intro h
    subst w
    simpa using hnodup
  by_cases hablt : a < b
  · exact sortedPair_arbitraryTriple_hasCanonicalConfig
      ha hb hu hv hw hablt huv huw hvw
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [SamePairPermutation]) hrad
  · have hbalt : b < a := by omega
    exact sortedPair_arbitraryTriple_hasCanonicalConfig
      hb ha hu hv hw hbalt huv huw hvw
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [SamePairPermutation]) hrad

section Topological

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Combining index normalization with the Round 23 forcing theorem removes
all pair/triple ordering assumptions from the fivefold contradiction. -/
theorem arbitraryOrderedFive_strictRadon_contradicts_noFiveDistinctActive
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
    {a b u v w : Nat}
    (ha : a < 7) (hb : b < 7)
    (hu : u < 7) (hv : v < 7) (hw : w < 7)
    (hnodup : [a, b, u, v, w].Nodup)
    (hrad : StrictRadon23 (P a) (P b) (P u) (P v) (P w)) : False := by
  obtain ⟨cfg, hcfg, hradCanonical⟩ :=
    arbitraryOrderedFive_strictRadon_hasCanonicalConfig
      ha hb hu hv hw hnodup hrad
  exact every_fano_radon_config_contradicts_noFiveDistinctActive
    hopen hconv hpoint hsun hcore hno5 cfg hcfg hradCanonical

end Topological

#print axioms StrictRadon23.reorderLeft
#print axioms canonicalRadonConfig_mem_allRadonConfigs
#print axioms canonicalized_orderedFive_hasCanonicalConfig
#print axioms arbitraryOrderedFive_strictRadon_hasCanonicalConfig
#print axioms arbitraryOrderedFive_strictRadon_contradicts_noFiveDistinctActive

end FanoLowerBound
