import FanoLowerBound.DirectFivePointRadon
import FanoLowerBound.OnePositiveRebaseOther

/-!
# Direct six-point Radon branches

This module packages the six two-positive and four three-positive barycentric
sign patterns into `HasStrictRadon23`.  The unused sixth point is placed in the
omitted basis slot of the certificate permutation.
-/

namespace FanoLowerBound

private def twoPerm01 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 3, 4, 1]
  invFun := ![0, 5, 2, 3, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def twoPerm02 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 3, 4, 2]
  invFun := ![0, 2, 5, 3, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def twoPerm03 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 4, 3]
  invFun := ![0, 2, 3, 5, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def twoPerm12 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 3, 4, 2]
  invFun := ![2, 0, 5, 3, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def twoPerm13 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 4, 3]
  invFun := ![2, 0, 3, 5, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def twoPerm23 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def threePermNeg3 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def threePermNeg2 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def threePermNeg1 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def threePermNeg0 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private theorem packTwo01
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 0) (p 1) (p 4) (p 2) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm01, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm01, baseEmb, Function.comp_def] using h

private theorem packTwo02
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 0) (p 2) (p 4) (p 1) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm02, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm02, baseEmb, Function.comp_def] using h

private theorem packTwo03
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 0) (p 3) (p 4) (p 1) (p 2)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm03, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm03, baseEmb, Function.comp_def] using h

private theorem packTwo12
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 1) (p 2) (p 4) (p 0) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm12, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm12, baseEmb, Function.comp_def] using h

private theorem packTwo13
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 1) (p 3) (p 4) (p 0) (p 2)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm13, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm13, baseEmb, Function.comp_def] using h

private theorem packTwo23
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 2) (p 3) (p 4) (p 0) (p 1)) :
    HasStrictRadon23 p := by
  refine ⟨twoPerm23, Equiv.refl _, Or.inl ?_⟩
  simpa [twoPerm23, baseEmb, Function.comp_def] using h

private theorem packThreeNeg3
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 4) (p 3) (p 0) (p 1) (p 2)) :
    HasStrictRadon23 p := by
  refine ⟨threePermNeg3, Equiv.refl _, Or.inl ?_⟩
  simpa [threePermNeg3, baseEmb, Function.comp_def] using h

private theorem packThreeNeg2
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 4) (p 2) (p 0) (p 1) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨threePermNeg2, Equiv.refl _, Or.inl ?_⟩
  simpa [threePermNeg2, baseEmb, Function.comp_def] using h

private theorem packThreeNeg1
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 4) (p 1) (p 0) (p 2) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨threePermNeg1, Equiv.refl _, Or.inl ?_⟩
  simpa [threePermNeg1, baseEmb, Function.comp_def] using h

private theorem packThreeNeg0
    (p : Fin 6 → Point3) (h : StrictRadon23 (p 4) (p 0) (p 1) (p 2) (p 3)) :
    HasStrictRadon23 p := by
  refine ⟨threePermNeg0, Equiv.refl _, Or.inl ?_⟩
  simpa [threePermNeg0, baseEmb, Function.comp_def] using h

/-- Direct branch with positive coordinates `0,1`. -/
theorem twoPositive01_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : a2 < 0) (ha3 : a3 < 0) :
    HasStrictRadon23 p :=
  packTwo01 p (two_positive_direct_strictRadon23
    (p 0) (p 1) (p 2) (p 3) (p 4) a0 a1 a2 a3 hq ha ha0 ha1 ha2 ha3)

/-- Direct branch with positive coordinates `0,2`. -/
theorem twoPositive02_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : a1 < 0) (ha2 : 0 < a2) (ha3 : a3 < 0) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a0 • p 0 + a2 • p 2 + a1 • p 1 + a3 • p 3 := by
    rw [hq]
    module
  have ha' : a0 + a2 + a1 + a3 = 1 := by linarith
  exact packTwo02 p (two_positive_direct_strictRadon23
    (p 0) (p 2) (p 1) (p 3) (p 4) a0 a2 a1 a3 hq' ha' ha0 ha2 ha1 ha3)

/-- Direct branch with positive coordinates `0,3`. -/
theorem twoPositive03_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : a1 < 0) (ha2 : a2 < 0) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a0 • p 0 + a3 • p 3 + a1 • p 1 + a2 • p 2 := by
    rw [hq]
    module
  have ha' : a0 + a3 + a1 + a2 = 1 := by linarith
  exact packTwo03 p (two_positive_direct_strictRadon23
    (p 0) (p 3) (p 1) (p 2) (p 4) a0 a3 a1 a2 hq' ha' ha0 ha3 ha1 ha2)

/-- Direct branch with positive coordinates `1,2`. -/
theorem twoPositive12_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : a0 < 0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : a3 < 0) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a1 • p 1 + a2 • p 2 + a0 • p 0 + a3 • p 3 := by
    rw [hq]
    module
  have ha' : a1 + a2 + a0 + a3 = 1 := by linarith
  exact packTwo12 p (two_positive_direct_strictRadon23
    (p 1) (p 2) (p 0) (p 3) (p 4) a1 a2 a0 a3 hq' ha' ha1 ha2 ha0 ha3)

/-- Direct branch with positive coordinates `1,3`. -/
theorem twoPositive13_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : a0 < 0) (ha1 : 0 < a1) (ha2 : a2 < 0) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a1 • p 1 + a3 • p 3 + a0 • p 0 + a2 • p 2 := by
    rw [hq]
    module
  have ha' : a1 + a3 + a0 + a2 = 1 := by linarith
  exact packTwo13 p (two_positive_direct_strictRadon23
    (p 1) (p 3) (p 0) (p 2) (p 4) a1 a3 a0 a2 hq' ha' ha1 ha3 ha0 ha2)

/-- Direct branch with positive coordinates `2,3`. -/
theorem twoPositive23_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : a0 < 0) (ha1 : a1 < 0) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a2 • p 2 + a3 • p 3 + a0 • p 0 + a1 • p 1 := by
    rw [hq]
    module
  have ha' : a2 + a3 + a0 + a1 = 1 := by linarith
  exact packTwo23 p (two_positive_direct_strictRadon23
    (p 2) (p 3) (p 0) (p 1) (p 4) a2 a3 a0 a1 hq' ha' ha2 ha3 ha0 ha1)

/-- Direct branch with negative coordinate `3`. -/
theorem threePositiveNeg3_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : a3 < 0) :
    HasStrictRadon23 p :=
  packThreeNeg3 p (three_positive_direct_strictRadon23
    (p 0) (p 1) (p 2) (p 3) (p 4) a0 a1 a2 a3 hq ha ha0 ha1 ha2 ha3)

/-- Direct branch with negative coordinate `2`. -/
theorem threePositiveNeg2_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : a2 < 0) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a0 • p 0 + a1 • p 1 + a3 • p 3 + a2 • p 2 := by
    rw [hq]
    module
  have ha' : a0 + a1 + a3 + a2 = 1 := by linarith
  exact packThreeNeg2 p (three_positive_direct_strictRadon23
    (p 0) (p 1) (p 3) (p 2) (p 4) a0 a1 a3 a2 hq' ha' ha0 ha1 ha3 ha2)

/-- Direct branch with negative coordinate `1`. -/
theorem threePositiveNeg1_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : 0 < a0) (ha1 : a1 < 0) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a0 • p 0 + a2 • p 2 + a3 • p 3 + a1 • p 1 := by
    rw [hq]
    module
  have ha' : a0 + a2 + a3 + a1 = 1 := by linarith
  exact packThreeNeg1 p (three_positive_direct_strictRadon23
    (p 0) (p 2) (p 3) (p 1) (p 4) a0 a2 a3 a1 hq' ha' ha0 ha2 ha3 ha1)

/-- Direct branch with negative coordinate `0`. -/
theorem threePositiveNeg0_sixPoint_hasStrictRadon23
    (p : Fin 6 → Point3) (a0 a1 a2 a3 : ℝ)
    (hq : p 4 = a0 • p 0 + a1 • p 1 + a2 • p 2 + a3 • p 3)
    (ha : a0 + a1 + a2 + a3 = 1)
    (ha0 : a0 < 0) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    HasStrictRadon23 p := by
  have hq' : p 4 = a1 • p 1 + a2 • p 2 + a3 • p 3 + a0 • p 0 := by
    rw [hq]
    module
  have ha' : a1 + a2 + a3 + a0 = 1 := by linarith
  exact packThreeNeg0 p (three_positive_direct_strictRadon23
    (p 1) (p 2) (p 3) (p 0) (p 4) a1 a2 a3 a0 hq' ha' ha1 ha2 ha3 ha0)

#print axioms twoPositive01_sixPoint_hasStrictRadon23
#print axioms twoPositive02_sixPoint_hasStrictRadon23
#print axioms twoPositive03_sixPoint_hasStrictRadon23
#print axioms twoPositive12_sixPoint_hasStrictRadon23
#print axioms twoPositive13_sixPoint_hasStrictRadon23
#print axioms twoPositive23_sixPoint_hasStrictRadon23
#print axioms threePositiveNeg0_sixPoint_hasStrictRadon23
#print axioms threePositiveNeg1_sixPoint_hasStrictRadon23
#print axioms threePositiveNeg2_sixPoint_hasStrictRadon23
#print axioms threePositiveNeg3_sixPoint_hasStrictRadon23

end FanoLowerBound
