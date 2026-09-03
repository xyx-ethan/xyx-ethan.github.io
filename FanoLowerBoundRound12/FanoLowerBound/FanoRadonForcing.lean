import FanoLowerBound.GeneralLineCore
import FanoLowerBound.FanoForcingTable

/-!
# Semantic Fano--Radon forcing

This module connects the finite 210-record Fano incidence table to the
kernel-certified strict Radon and open-convex sunflower segment theorems.
For every certified 2-side/3-side configuration, the common Radon point is
forced into five pairwise distinct neuron sets.
-/

namespace FanoLowerBound

open AffineMap Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The six possible orders of the same three labels. -/
def SameTriplePermutation (e₁ e₂ e₃ x y z : Nat) : Prop :=
  (e₁ = x ∧ e₂ = y ∧ e₃ = z) ∨
  (e₁ = x ∧ e₂ = z ∧ e₃ = y) ∨
  (e₁ = y ∧ e₂ = x ∧ e₃ = z) ∨
  (e₁ = y ∧ e₂ = z ∧ e₃ = x) ∨
  (e₁ = z ∧ e₂ = x ∧ e₃ = y) ∨
  (e₁ = z ∧ e₂ = y ∧ e₃ = x)

/-- The part of a finite Fano forcing certificate used by the geometric proof. -/
def FanoForcingCert.GeomValid (c : FanoForcingCert) : Prop :=
  hasPoint c.pairA c.i = true ∧
  hasPoint c.pairB c.i = true ∧
  lineContains3 c.i c.j c.k = true ∧
  SameTriplePermutation c.edge1 c.edge2 c.apex
    c.triple0 c.triple1 c.triple2 ∧
  hasPoint c.edge1 c.j = true ∧
  hasPoint c.edge2 c.j = true ∧
  hasPoint c.apex c.k = true ∧
  hasPoint c.pairA c.a = true ∧
  hasPoint c.pairB c.b = true ∧
  [c.i, c.j, c.k, c.a, c.b].Nodup ∧
  lineContains3 c.a c.b c.k = true

/-- Every one of the 210 stored records has the semantic incidence data needed
by the two-sunflower argument. -/
theorem all_fano_forcing_certificates_geom_valid :
    fanoForcingCertificates.all (fun c => decide c.GeomValid) = true := by
  native_decide

/-- Extract semantic validity for an arbitrary record occurring in the table. -/
theorem FanoForcingCert.geomValid_of_mem {c : FanoForcingCert}
    (hc : c ∈ fanoForcingCertificates) : c.GeomValid := by
  have hdec : decide c.GeomValid = true :=
    (List.all_eq_true.mp all_fano_forcing_certificates_geom_valid) c hc
  exact of_decide_eq_true hdec

/-- Strict `2--3` Radon equality is invariant under any permutation of the
three-point side. -/
theorem StrictRadon23.reorderRight
    {x₀ x₁ : E} {P : Nat → E}
    {e₁ e₂ e₃ x y z : Nat}
    (hperm : SameTriplePermutation e₁ e₂ e₃ x y z)
    (h : StrictRadon23 x₀ x₁ (P x) (P y) (P z)) :
    StrictRadon23 x₀ x₁ (P e₁) (P e₂) (P e₃) := by
  rcases h with ⟨a₀, a₁, b₀, b₁, b₂,
    ha₀, ha₁, hb₀, hb₁, hb₂, hasum, hbsum, heq⟩
  rcases hperm with hxyz | hxzy | hyxz | hyzx | hzxy | hzyx
  · rcases hxyz with ⟨rfl, rfl, rfl⟩
    exact ⟨a₀, a₁, b₀, b₁, b₂,
      ha₀, ha₁, hb₀, hb₁, hb₂, hasum, hbsum, heq⟩
  · rcases hxzy with ⟨rfl, rfl, rfl⟩
    refine ⟨a₀, a₁, b₀, b₂, b₁,
      ha₀, ha₁, hb₀, hb₂, hb₁, hasum, ?_, ?_⟩
    · linarith
    · calc
        a₀ • x₀ + a₁ • x₁ = b₀ • P x + b₁ • P y + b₂ • P z := heq
        _ = b₀ • P x + b₂ • P z + b₁ • P y := by abel
  · rcases hyxz with ⟨rfl, rfl, rfl⟩
    refine ⟨a₀, a₁, b₁, b₀, b₂,
      ha₀, ha₁, hb₁, hb₀, hb₂, hasum, ?_, ?_⟩
    · linarith
    · calc
        a₀ • x₀ + a₁ • x₁ = b₀ • P x + b₁ • P y + b₂ • P z := heq
        _ = b₁ • P y + b₀ • P x + b₂ • P z := by abel
  · rcases hyzx with ⟨rfl, rfl, rfl⟩
    refine ⟨a₀, a₁, b₁, b₂, b₀,
      ha₀, ha₁, hb₁, hb₂, hb₀, hasum, ?_, ?_⟩
    · linarith
    · calc
        a₀ • x₀ + a₁ • x₁ = b₀ • P x + b₁ • P y + b₂ • P z := heq
        _ = b₁ • P y + b₂ • P z + b₀ • P x := by abel
  · rcases hzxy with ⟨rfl, rfl, rfl⟩
    refine ⟨a₀, a₁, b₂, b₀, b₁,
      ha₀, ha₁, hb₂, hb₀, hb₁, hasum, ?_, ?_⟩
    · linarith
    · calc
        a₀ • x₀ + a₁ • x₁ = b₀ • P x + b₁ • P y + b₂ • P z := heq
        _ = b₂ • P z + b₀ • P x + b₁ • P y := by abel
  · rcases hzyx with ⟨rfl, rfl, rfl⟩
    refine ⟨a₀, a₁, b₂, b₁, b₀,
      ha₀, ha₁, hb₂, hb₁, hb₀, hasum, ?_, ?_⟩
    · linarith
    · calc
        a₀ • x₀ + a₁ • x₁ = b₀ • P x + b₁ • P y + b₂ • P z := heq
        _ = b₂ • P z + b₁ • P y + b₀ • P x := by abel

/-- A five-fold active witness, with the five neuron labels certified distinct. -/
def FivefoldFanoWitness (U : Nat → Set E) (c : FanoForcingCert) : Prop :=
  ∃ q : E,
    q ∈ U c.i ∧ q ∈ U c.j ∧ q ∈ U c.k ∧
    q ∈ U c.a ∧ q ∈ U c.b ∧
    [c.i, c.j, c.k, c.a, c.b].Nodup

/-- One geometrically valid Fano record turns its strict Radon equality into a
five-fold active point by two applications of the open-convex sunflower
segment theorem. -/
theorem FanoForcingCert.forcesFivefold
    {U : Nat → Set E} {P : Nat → E}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : E, InThreeCore (U x) (U y) (U z) q)
    (c : FanoForcingCert) (hc : c.GeomValid)
    (hrad : StrictRadon23 (P c.pairA) (P c.pairB)
      (P c.edge1) (P c.edge2) (P c.apex)) :
    FivefoldFanoWitness U c := by
  rcases hc with ⟨hAi, hBi, hijk, hperm,
    hE₁j, hE₂j, hAk, hAa, hBb, hnodup, habk⟩
  rcases hrad with ⟨αA, αB, β₁, β₂, β₃,
    hαA, hαB, hβ₁, hβ₂, hβ₃, hαsum, hβsum, heq⟩
  let q : E := αA • P c.pairA + αB • P c.pairB
  let s : ℝ := β₁ + β₂
  let r : ℝ := β₂ / s
  let qedge : E := lineMap (P c.edge1) (P c.edge2) r
  have hspos : 0 < s := by dsimp [s]; linarith
  have hslt : s < 1 := by dsimp [s]; linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hrpos : 0 < r := by dsimp [r]; exact div_pos hβ₂ hspos
  have hrlt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hspos).2 (by dsimp [s]; linarith)
  have hqPairEq : q = lineMap (P c.pairA) (P c.pairB) αB := by
    dsimp [q]
    rw [lineMap_apply_module]
    have hcoef : 1 - αB = αA := by linarith
    rw [hcoef]
  have hαBlt : αB < 1 := by linarith
  have hqPairSeg : q ∈ segment ℝ (P c.pairA) (P c.pairB) := by
    rw [hqPairEq]
    exact lineMap_mem_segment ℝ _ _ ⟨hαB.le, hαBlt.le⟩
  have hqUi : q ∈ U c.i :=
    (hconv c.i).segment_subset
      (hpoint c.pairA c.i hAi) (hpoint c.pairB c.i hBi) hqPairSeg
  have hqedgeSeg : qedge ∈ segment ℝ (P c.edge1) (P c.edge2) := by
    dsimp [qedge]
    exact lineMap_mem_segment ℝ _ _ ⟨hrpos.le, hrlt.le⟩
  have hqedgeUj : qedge ∈ U c.j :=
    (hconv c.j).segment_subset
      (hpoint c.edge1 c.j hE₁j) (hpoint c.edge2 c.j hE₂j) hqedgeSeg
  have hqRight : q = β₁ • P c.edge1 + β₂ • P c.edge2 + β₃ • P c.apex := by
    dsimp [q]
    exact heq
  have h1s : 1 - s = β₃ := by dsimp [s]; linarith
  have hsr : s * r = β₂ := by
    dsimp [r]
    field_simp [hsne]
  have hs1r : s * (1 - r) = β₁ := by
    calc
      s * (1 - r) = s - s * r := by ring
      _ = s - β₂ := by rw [hsr]
      _ = β₁ := by dsimp [s]; ring
  have hqApexEq : q = lineMap (P c.apex) qedge s := by
    rw [hqRight]
    dsimp [qedge]
    rw [lineMap_apply_module, lineMap_apply_module]
    simp only [smul_add, smul_smul]
    rw [h1s, hs1r, hsr]
    abel
  have hqApexSeg : q ∈ segment ℝ (P c.apex) qedge := by
    rw [hqApexEq]
    exact lineMap_mem_segment ℝ _ _ ⟨hspos.le, hslt.le⟩
  have hfirst : InThreeCore (U c.i) (U c.j) (U c.k) q :=
    openConvexThreeSunflower_segment_forcing
      (hopen c.i) (hopen c.j) (hopen c.k)
      (hconv c.i) (hconv c.j) (hconv c.k)
      (hsun c.i c.j c.k hijk) (hcore c.i c.j c.k hijk)
      hqUi hqedgeUj (hpoint c.apex c.k hAk) hqApexSeg
  have hsecond : InThreeCore (U c.a) (U c.b) (U c.k) q :=
    openConvexThreeSunflower_segment_forcing
      (hopen c.a) (hopen c.b) (hopen c.k)
      (hconv c.a) (hconv c.b) (hconv c.k)
      (hsun c.a c.b c.k habk) (hcore c.a c.b c.k habk)
      (hpoint c.pairA c.a hAa) (hpoint c.pairB c.b hBb)
      hfirst.2.2 hqPairSeg
  exact ⟨q, hfirst.1, hfirst.2.1, hfirst.2.2,
    hsecond.1, hsecond.2.1, hnodup⟩

/-- Every record in the 210-entry table semantically forces a five-fold point. -/
theorem all_fano_forcing_records_forceFivefold
    {U : Nat → Set E} {P : Nat → E}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : E, InThreeCore (U x) (U y) (U z) q) :
    ∀ c ∈ fanoForcingCertificates,
      StrictRadon23 (P c.pairA) (P c.pairB)
        (P c.edge1) (P c.edge2) (P c.apex) →
      FivefoldFanoWitness U c := by
  intro c hc hrad
  exact c.forcesFivefold hopen hconv hpoint hsun hcore
    c.geomValid_of_mem hc hrad

/-- Completeness form: every one of the 210 canonical pair/triple Radon
configurations has a table record, and after reordering the three-point side
that record forces a five-fold active witness. -/
theorem every_fano_radon_config_forcesFivefold
    {U : Nat → Set E} {P : Nat → E}
    (hopen : ∀ n : Nat, IsOpen (U n))
    (hconv : ∀ n : Nat, Convex ℝ (U n))
    (hpoint : ∀ line point : Nat,
      hasPoint line point = true → P line ∈ U point)
    (hsun : ∀ x y z : Nat,
      lineContains3 x y z = true → IsThreeSunflower (U x) (U y) (U z))
    (hcore : ∀ x y z : Nat,
      lineContains3 x y z = true → ∃ q : E, InThreeCore (U x) (U y) (U z) q)
    (cfg : RadonConfig) (hcfg : cfg ∈ allRadonConfigs)
    (hrad : StrictRadon23 (P cfg.pairA) (P cfg.pairB)
      (P cfg.triple0) (P cfg.triple1) (P cfg.triple2)) :
    ∃ c ∈ fanoForcingCertificates,
      c.toRadonConfig = cfg ∧ FivefoldFanoWitness U c := by
  have hcfgFin : cfg ∈ allRadonConfigs.toFinset := by simpa using hcfg
  have hmapFin : cfg ∈
      (fanoForcingCertificates.map FanoForcingCert.toRadonConfig).toFinset := by
    rw [fano_forcing_table_complete]
    exact hcfgFin
  have hmap : cfg ∈
      fanoForcingCertificates.map FanoForcingCert.toRadonConfig := by
    simpa using hmapFin
  rcases List.mem_map.mp hmap with ⟨c, hc, hceq⟩
  have hgeom : c.GeomValid := c.geomValid_of_mem hc
  have hrad0 : StrictRadon23 (P c.pairA) (P c.pairB)
      (P c.triple0) (P c.triple1) (P c.triple2) := by
    rw [hceq]
    exact hrad
  have hrad1 : StrictRadon23 (P c.pairA) (P c.pairB)
      (P c.edge1) (P c.edge2) (P c.apex) :=
    hrad0.reorderRight hgeom.2.2.2.1
  exact ⟨c, hc, hceq,
    c.forcesFivefold hopen hconv hpoint hsun hcore hgeom hrad1⟩

/-- A direct contradiction corollary for systems forbidding five pairwise
distinct simultaneously active neuron labels. -/
def NoFiveDistinctActive (U : Nat → Set E) : Prop :=
  ∀ q i j k a b,
    [i, j, k, a, b].Nodup →
    ¬(q ∈ U i ∧ q ∈ U j ∧ q ∈ U k ∧ q ∈ U a ∧ q ∈ U b)

theorem every_fano_radon_config_contradicts_noFiveDistinctActive
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
    (cfg : RadonConfig) (hcfg : cfg ∈ allRadonConfigs)
    (hrad : StrictRadon23 (P cfg.pairA) (P cfg.pairB)
      (P cfg.triple0) (P cfg.triple1) (P cfg.triple2)) : False := by
  obtain ⟨c, _, _, q, hqi, hqj, hqk, hqa, hqb, hnodup⟩ :=
    every_fano_radon_config_forcesFivefold
      hopen hconv hpoint hsun hcore cfg hcfg hrad
  exact hno5 q c.i c.j c.k c.a c.b hnodup
    ⟨hqi, hqj, hqk, hqa, hqb⟩

#print axioms all_fano_forcing_certificates_geom_valid
#print axioms FanoForcingCert.geomValid_of_mem
#print axioms StrictRadon23.reorderRight
#print axioms FanoForcingCert.forcesFivefold
#print axioms all_fano_forcing_records_forceFivefold
#print axioms every_fano_radon_config_forcesFivefold
#print axioms every_fano_radon_config_contradicts_noFiveDistinctActive

end FanoLowerBound
