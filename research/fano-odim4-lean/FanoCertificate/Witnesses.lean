import FanoCertificate.Core

namespace FanoOdim4

def point4 (a b c d : ℝ) : Point := fun i =>
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

def w123 : Point := point4 (-3 : ℝ) (9 : ℝ) (-27 : ℝ) (81 : ℝ)
theorem witness123 : HasPattern w123 pat123 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w123, pat123, U1, U2, U3, U4, U5, U6, U7, L]

def w145 : Point := point4 (-2 : ℝ) (4 : ℝ) (-8 : ℝ) (16 : ℝ)
theorem witness145 : HasPattern w145 pat145 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w145, pat145, U1, U2, U3, U4, U5, U6, U7, L]

def w167 : Point := point4 (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ)
theorem witness167 : HasPattern w167 pat167 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w167, pat167, U1, U2, U3, U4, U5, U6, U7, L]

def w246 : Point := point4 (-1 : ℝ) (1 : ℝ) (-1 : ℝ) (1 : ℝ)
theorem witness246 : HasPattern w246 pat246 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w246, pat246, U1, U2, U3, U4, U5, U6, U7, L]

def w257 : Point := point4 (3 : ℝ) (9 : ℝ) (27 : ℝ) (81 : ℝ)
theorem witness257 : HasPattern w257 pat257 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w257, pat257, U1, U2, U3, U4, U5, U6, U7, L]

def w347 : Point := point4 (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)
theorem witness347 : HasPattern w347 pat347 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w347, pat347, U1, U2, U3, U4, U5, U6, U7, L]

def w356 : Point := point4 (2 : ℝ) (4 : ℝ) (8 : ℝ) (16 : ℝ)
theorem witness356 : HasPattern w356 pat356 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w356, pat356, U1, U2, U3, U4, U5, U6, U7, L]

def w1 : Point := point4 ((-5 : ℝ) / 3) ((13 : ℝ) / 3) ((-35 : ℝ) / 3) ((97 : ℝ) / 3)
theorem witness1 : HasPattern w1 pat1 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w1, pat1, U1, U2, U3, U4, U5, U6, U7, L]

def w2 : Point := point4 ((-1 : ℝ) / 3) ((19 : ℝ) / 3) ((-1 : ℝ) / 3) ((163 : ℝ) / 3)
theorem witness2 : HasPattern w2 pat2 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w2, pat2, U1, U2, U3, U4, U5, U6, U7, L]

def w3 : Point := point4 (0 : ℝ) ((14 : ℝ) / 3) (-6 : ℝ) ((98 : ℝ) / 3)
theorem witness3 : HasPattern w3 pat3 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w3, pat3, U1, U2, U3, U4, U5, U6, U7, L]

def w4 : Point := point4 ((-2 : ℝ) / 3) (2 : ℝ) ((-8 : ℝ) / 3) (6 : ℝ)
theorem witness4 : HasPattern w4 pat4 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w4, pat4, U1, U2, U3, U4, U5, U6, U7, L]

def w5 : Point := point4 (1 : ℝ) ((17 : ℝ) / 3) (9 : ℝ) ((113 : ℝ) / 3)
theorem witness5 : HasPattern w5 pat5 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w5, pat5, U1, U2, U3, U4, U5, U6, U7, L]

def w6 : Point := point4 ((1 : ℝ) / 3) ((5 : ℝ) / 3) ((7 : ℝ) / 3) ((17 : ℝ) / 3)
theorem witness6 : HasPattern w6 pat6 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w6, pat6, U1, U2, U3, U4, U5, U6, U7, L]

def w7 : Point := point4 ((4 : ℝ) / 3) ((10 : ℝ) / 3) ((28 : ℝ) / 3) ((82 : ℝ) / 3)
theorem witness7 : HasPattern w7 pat7 := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, w7, pat7, U1, U2, U3, U4, U5, U6, U7, L]

def wEmpty : Point := point4 (10000 : ℝ) (10000 : ℝ) (10000 : ℝ) (10000 : ℝ)
theorem witnessEmpty : HasPattern wEmpty patEmpty := by
  intro i
  fin_cases i <;> norm_num [HasPattern, U, point4, wEmpty, patEmpty, U1, U2, U3, U4, U5, U6, U7, L]

end FanoOdim4
