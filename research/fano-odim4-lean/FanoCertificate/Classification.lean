import FanoCertificate.Pairs1
import FanoCertificate.Pairs2
import FanoCertificate.Pairs3
import FanoCertificate.NoSeven
import FanoCertificate.Witnesses

namespace FanoOdim4

theorem classifyAtoms (x : Point) :
  AtomEmpty x ∨
  Atom1 x ∨
  Atom2 x ∨
  Atom3 x ∨
  Atom4 x ∨
  Atom5 x ∨
  Atom6 x ∨
  Atom7 x ∨
  Atom123 x ∨
  Atom145 x ∨
  Atom167 x ∨
  Atom246 x ∨
  Atom257 x ∨
  Atom347 x ∨
  Atom356 x := by
  have hp_1_2_3 : U1 x → U2 x → U3 x := fun hi hj => pair_1_2_3 hi hj
  have hp_1_3_2 : U1 x → U3 x → U2 x := fun hi hj => pair_1_3_2 hi hj
  have hp_1_4_5 : U1 x → U4 x → U5 x := fun hi hj => pair_1_4_5 hi hj
  have hp_1_5_4 : U1 x → U5 x → U4 x := fun hi hj => pair_1_5_4 hi hj
  have hp_1_6_7 : U1 x → U6 x → U7 x := fun hi hj => pair_1_6_7 hi hj
  have hp_1_7_6 : U1 x → U7 x → U6 x := fun hi hj => pair_1_7_6 hi hj
  have hp_2_3_1 : U2 x → U3 x → U1 x := fun hi hj => pair_2_3_1 hi hj
  have hp_2_4_6 : U2 x → U4 x → U6 x := fun hi hj => pair_2_4_6 hi hj
  have hp_2_5_7 : U2 x → U5 x → U7 x := fun hi hj => pair_2_5_7 hi hj
  have hp_2_6_4 : U2 x → U6 x → U4 x := fun hi hj => pair_2_6_4 hi hj
  have hp_2_7_5 : U2 x → U7 x → U5 x := fun hi hj => pair_2_7_5 hi hj
  have hp_3_4_7 : U3 x → U4 x → U7 x := fun hi hj => pair_3_4_7 hi hj
  have hp_3_5_6 : U3 x → U5 x → U6 x := fun hi hj => pair_3_5_6 hi hj
  have hp_3_6_5 : U3 x → U6 x → U5 x := fun hi hj => pair_3_6_5 hi hj
  have hp_3_7_4 : U3 x → U7 x → U4 x := fun hi hj => pair_3_7_4 hi hj
  have hp_4_5_1 : U4 x → U5 x → U1 x := fun hi hj => pair_4_5_1 hi hj
  have hp_4_6_2 : U4 x → U6 x → U2 x := fun hi hj => pair_4_6_2 hi hj
  have hp_4_7_3 : U4 x → U7 x → U3 x := fun hi hj => pair_4_7_3 hi hj
  have hp_5_6_3 : U5 x → U6 x → U3 x := fun hi hj => pair_5_6_3 hi hj
  have hp_5_7_2 : U5 x → U7 x → U2 x := fun hi hj => pair_5_7_2 hi hj
  have hp_6_7_1 : U6 x → U7 x → U1 x := fun hi hj => pair_6_7_1 hi hj
  have h7 : ¬ (U1 x ∧ U2 x ∧ U3 x ∧ U4 x ∧ U5 x ∧ U6 x ∧ U7 x) := noSeven x
  simp only [AtomEmpty, Atom1, Atom2, Atom3, Atom4, Atom5, Atom6, Atom7, Atom123, Atom145, Atom167, Atom246, Atom257, Atom347, Atom356]
  tauto

theorem everyPointHasFPPattern (x : Point) :
  HasPattern x patEmpty ∨
  HasPattern x pat1 ∨
  HasPattern x pat2 ∨
  HasPattern x pat3 ∨
  HasPattern x pat4 ∨
  HasPattern x pat5 ∨
  HasPattern x pat6 ∨
  HasPattern x pat7 ∨
  HasPattern x pat123 ∨
  HasPattern x pat145 ∨
  HasPattern x pat167 ∨
  HasPattern x pat246 ∨
  HasPattern x pat257 ∨
  HasPattern x pat347 ∨
  HasPattern x pat356 := by
  rcases classifyAtoms x with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, AtomEmpty, patEmpty]
  · right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom1, pat1]
  · right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom2, pat2]
  · right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom3, pat3]
  · right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom4, pat4]
  · right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom5, pat5]
  · right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom6, pat6]
  · right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom7, pat7]
  · right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom123, pat123]
  · right; right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom145, pat145]
  · right; right; right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom167, pat167]
  · right; right; right; right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom246, pat246]
  · right; right; right; right; right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom257, pat257]
  · right; right; right; right; right; right; right; right; right; right; right; right; right; left
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom347, pat347]
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right
    intro i
    fin_cases i <;> simp_all [HasPattern, U, Atom356, pat356]

theorem code_eq_FP : Code = FPSet := by
  ext s
  constructor
  · rintro ⟨x, hx⟩
    rcases everyPointHasFPPattern x with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h0 i)
    · right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h1 i)
    · right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h2 i)
    · right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h3 i)
    · right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h4 i)
    · right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h5 i)
    · right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h6 i)
    · right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h7 i)
    · right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h8 i)
    · right; right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h9 i)
    · right; right; right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h10 i)
    · right; right; right; right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h11 i)
    · right; right; right; right; right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h12 i)
    · right; right; right; right; right; right; right; right; right; right; right; right; right; left
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h13 i)
    · right; right; right; right; right; right; right; right; right; right; right; right; right; right
      apply Finset.ext
      intro i
      exact (hx i).symm.trans (h14 i)
  · intro hs
    change s = patEmpty ∨ s = pat1 ∨ s = pat2 ∨ s = pat3 ∨ s = pat4 ∨ s = pat5 ∨ s = pat6 ∨ s = pat7 ∨ s = pat123 ∨ s = pat145 ∨ s = pat167 ∨ s = pat246 ∨ s = pat257 ∨ s = pat347 ∨ s = pat356 at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · subst s
      exact ⟨wEmpty, witnessEmpty⟩
    · subst s
      exact ⟨w1, witness1⟩
    · subst s
      exact ⟨w2, witness2⟩
    · subst s
      exact ⟨w3, witness3⟩
    · subst s
      exact ⟨w4, witness4⟩
    · subst s
      exact ⟨w5, witness5⟩
    · subst s
      exact ⟨w6, witness6⟩
    · subst s
      exact ⟨w7, witness7⟩
    · subst s
      exact ⟨w123, witness123⟩
    · subst s
      exact ⟨w145, witness145⟩
    · subst s
      exact ⟨w167, witness167⟩
    · subst s
      exact ⟨w246, witness246⟩
    · subst s
      exact ⟨w257, witness257⟩
    · subst s
      exact ⟨w347, witness347⟩
    · subst s
      exact ⟨w356, witness356⟩

#print axioms code_eq_FP

end FanoOdim4
