import FanoCertificate.Core

namespace FanoOdim4

theorem noSeven (x : Point) : ¬ (U1 x ∧ U2 x ∧ U3 x ∧ U4 x ∧ U5 x ∧ U6 x ∧ U7 x) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp only [U1] at h1
  rcases h1 with ⟨h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9⟩
  simp only [U2] at h2
  rcases h2 with ⟨h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10⟩
  simp only [U4] at h4
  rcases h4 with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  have t0 : (1563715 : ℝ) * L (-487500 : ℝ) (687500 : ℝ) (487500 : ℝ) (77500 : ℝ) x < (1563715 : ℝ) * (1065003 : ℝ) :=
    mul_lt_mul_of_pos_left h1_3 (by norm_num)
  have t1 : (2754063 : ℝ) * L (0 : ℝ) (37500 : ℝ) (-6250 : ℝ) (-6250 : ℝ) x < (2754063 : ℝ) * (100001 : ℝ) :=
    mul_lt_mul_of_pos_left h1_5 (by norm_num)
  have t2 : (918021 : ℝ) * L (50000 : ℝ) (2262500 : ℝ) (-31250 : ℝ) (-556250 : ℝ) x < (918021 : ℝ) * (300003 : ℝ) :=
    mul_lt_mul_of_pos_left h1_7 (by norm_num)
  have t3 : (38652 : ℝ) * L (5787500 : ℝ) (0 : ℝ) (-5787500 : ℝ) (-1725000 : ℝ) x < (38652 : ℝ) * (-824991 : ℝ) :=
    mul_lt_mul_of_pos_left h2_7 (by norm_num)
  have t4 : (138305 : ℝ) * L (3562500 : ℝ) (-23537500 : ℝ) (-3562500 : ℝ) (3422500 : ℝ) x < (138305 : ℝ) * (-18014979 : ℝ) :=
    mul_lt_mul_of_pos_left h4_10 (by norm_num)
  have impossible : (0 : ℝ) < (-307269948456 : ℝ) := by
    calc
      (0 : ℝ) = (1563715 : ℝ) * L (-487500 : ℝ) (687500 : ℝ) (487500 : ℝ) (77500 : ℝ) x + (2754063 : ℝ) * L (0 : ℝ) (37500 : ℝ) (-6250 : ℝ) (-6250 : ℝ) x + (918021 : ℝ) * L (50000 : ℝ) (2262500 : ℝ) (-31250 : ℝ) (-556250 : ℝ) x + (38652 : ℝ) * L (5787500 : ℝ) (0 : ℝ) (-5787500 : ℝ) (-1725000 : ℝ) x + (138305 : ℝ) * L (3562500 : ℝ) (-23537500 : ℝ) (-3562500 : ℝ) (3422500 : ℝ) x := by
        simp only [L]
        ring
      _ < (1563715 : ℝ) * (1065003 : ℝ) + (2754063 : ℝ) * (100001 : ℝ) + (918021 : ℝ) * (300003 : ℝ) + (38652 : ℝ) * (-824991 : ℝ) + (138305 : ℝ) * (-18014979 : ℝ) := by linarith only [t0, t1, t2, t3, t4]
      _ = (-307269948456 : ℝ) := by norm_num
  norm_num at impossible

end FanoOdim4
