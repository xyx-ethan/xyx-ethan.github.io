import FanoCertificate.Core

namespace FanoOdim4

def point4 (a b c d : ℝ) : Point := fun i =>
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

macro "verify_witness" w:term p:term : tactic =>
  `(tactic|
    intro i
    fin_cases i <;>
      simp [HasPattern, U, point4, $w, $p, U1, U2, U3, U4, U5, U6, U7, L] <;>
      norm_num)

def w123 : Point := point4 (-3 : ℝ) (9 : ℝ) (-27 : ℝ) (81 : ℝ)
theorem witness123 : HasPattern w123 pat123 := by verify_witness w123 pat123

def w145 : Point := point4 (-2 : ℝ) (4 : ℝ) (-8 : ℝ) (16 : ℝ)
theorem witness145 : HasPattern w145 pat145 := by verify_witness w145 pat145

def w167 : Point := point4 (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ)
theorem witness167 : HasPattern w167 pat167 := by verify_witness w167 pat167

def w246 : Point := point4 (-1 : ℝ) (1 : ℝ) (-1 : ℝ) (1 : ℝ)
theorem witness246 : HasPattern w246 pat246 := by verify_witness w246 pat246

def w257 : Point := point4 (3 : ℝ) (9 : ℝ) (27 : ℝ) (81 : ℝ)
theorem witness257 : HasPattern w257 pat257 := by verify_witness w257 pat257

def w347 : Point := point4 (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)
theorem witness347 : HasPattern w347 pat347 := by verify_witness w347 pat347

def w356 : Point := point4 (2 : ℝ) (4 : ℝ) (8 : ℝ) (16 : ℝ)
theorem witness356 : HasPattern w356 pat356 := by verify_witness w356 pat356

def w1 : Point := point4 ((-5 : ℝ) / 3) ((13 : ℝ) / 3) ((-35 : ℝ) / 3) ((97 : ℝ) / 3)
theorem witness1 : HasPattern w1 pat1 := by verify_witness w1 pat1

def w2 : Point := point4 ((-1 : ℝ) / 3) ((19 : ℝ) / 3) ((-1 : ℝ) / 3) ((163 : ℝ) / 3)
theorem witness2 : HasPattern w2 pat2 := by verify_witness w2 pat2

def w3 : Point := point4 (0 : ℝ) ((14 : ℝ) / 3) (-6 : ℝ) ((98 : ℝ) / 3)
theorem witness3 : HasPattern w3 pat3 := by verify_witness w3 pat3

def w4 : Point := point4 ((-2 : ℝ) / 3) (2 : ℝ) ((-8 : ℝ) / 3) (6 : ℝ)
theorem witness4 : HasPattern w4 pat4 := by verify_witness w4 pat4

def w5 : Point := point4 (1 : ℝ) ((17 : ℝ) / 3) (9 : ℝ) ((113 : ℝ) / 3)
theorem witness5 : HasPattern w5 pat5 := by verify_witness w5 pat5

def w6 : Point := point4 ((1 : ℝ) / 3) ((5 : ℝ) / 3) ((7 : ℝ) / 3) ((17 : ℝ) / 3)
theorem witness6 : HasPattern w6 pat6 := by verify_witness w6 pat6

def w7 : Point := point4 ((4 : ℝ) / 3) ((10 : ℝ) / 3) ((28 : ℝ) / 3) ((82 : ℝ) / 3)
theorem witness7 : HasPattern w7 pat7 := by verify_witness w7 pat7

def wEmpty : Point := point4 (10000 : ℝ) (10000 : ℝ) (10000 : ℝ) (10000 : ℝ)
theorem witnessEmpty : HasPattern wEmpty patEmpty := by verify_witness wEmpty patEmpty

end FanoOdim4
