import FanoCertificate.Core

namespace FanoOdim4

theorem pair_2_4_6 {x : Point} (hi : U2 x) (hj : U4 x) : U6 x := by
  simp only [U2] at hi
  simp only [U4] at hj
  rcases hi with ⟨h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10⟩
  rcases hj with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  simp only [U6]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4_3]
  · linarith only [h2_1, h2_8, h4_3, h4_5]
  · linarith only [h4_5]
  · linarith only [h2_1, h2_8, h4_3, h4_5]
  · linarith only [h2_1, h2_3, h2_8, h4_3]
  · linarith only [h2_1, h2_3, h2_8, h4_3]
  · linarith only [h2_1, h2_3, h2_8, h4_3]
  · linarith only [h2_1, h2_3, h2_8, h4_3]
  · linarith only [h2_8]
  · linarith only [h2_1, h2_3, h2_8, h4_3]

theorem pair_2_5_7 {x : Point} (hi : U2 x) (hj : U5 x) : U7 x := by
  simp only [U2] at hi
  simp only [U5] at hj
  rcases hi with ⟨h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10⟩
  rcases hj with ⟨h5_1, h5_2, h5_3, h5_4, h5_5, h5_6, h5_7, h5_8, h5_9, h5_10, h5_11⟩
  simp only [U7]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h2_2, h2_4, h2_9, h5_2]
  · linarith only [h5_2]
  · linarith only [h2_2, h2_9, h5_2, h5_3]
  · linarith only [h2_2]
  · linarith only [h2_4]
  · linarith only [h2_5, h2_9, h5_2, h5_3]
  · linarith only [h5_3]
  · linarith only [h2_2, h2_9, h5_2, h5_3]
  · linarith only [h2_2, h2_4, h2_9, h5_2]
  · linarith only [h2_2, h2_9, h5_2, h5_3]
  · linarith only [h2_2, h2_9, h5_2, h5_3]

theorem pair_2_6_4 {x : Point} (hi : U2 x) (hj : U6 x) : U4 x := by
  simp only [U2] at hi
  simp only [U6] at hj
  rcases hi with ⟨h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10⟩
  rcases hj with ⟨h6_1, h6_2, h6_3, h6_4, h6_5, h6_6, h6_7, h6_8, h6_9, h6_10⟩
  simp only [U4]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h2_1, h2_8, h6_1, h6_3]
  · linarith only [h2_1]
  · linarith only [h6_1]
  · linarith only [h2_3]
  · linarith only [h6_3]
  · linarith only [h2_1, h2_3, h2_8, h6_1]
  · linarith only [h2_1, h2_8, h6_1, h6_3]
  · linarith only [h2_1, h2_3, h2_8, h6_1]
  · linarith only [h2_1, h2_8, h6_1, h6_3]
  · linarith only [h2_1, h2_3, h2_8, h6_1]

theorem pair_2_7_5 {x : Point} (hi : U2 x) (hj : U7 x) : U5 x := by
  simp only [U2] at hi
  simp only [U7] at hj
  rcases hi with ⟨h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10⟩
  rcases hj with ⟨h7_1, h7_2, h7_3, h7_4, h7_5, h7_6, h7_7, h7_8, h7_9, h7_10, h7_11⟩
  simp only [U5]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h2_2, h2_4, h2_9, h7_2]
  · linarith only [h7_2]
  · linarith only [h7_7]
  · linarith only [h2_2, h2_9, h7_2, h7_7]
  · linarith only [h2_2, h2_4, h2_9, h7_2]
  · linarith only [h2_5]
  · linarith only [h2_2, h2_4, h2_9, h7_2]
  · linarith only [h2_2, h2_9, h7_2, h7_7]
  · linarith only [h2_2, h2_9, h7_2, h7_7]
  · linarith only [h2_9]
  · linarith only [h2_2, h2_9, h7_2, h7_7]

theorem pair_3_4_7 {x : Point} (hi : U3 x) (hj : U4 x) : U7 x := by
  simp only [U3] at hi
  simp only [U4] at hj
  rcases hi with ⟨h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11⟩
  rcases hj with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  simp only [U7]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h3_4, h3_6, h4_7, h4_9]
  · linarith only [h3_4, h3_6, h3_8, h4_9]
  · linarith only [h3_4]
  · linarith only [h3_4, h3_6, h4_7, h4_9]
  · linarith only [h3_4, h3_6, h4_7, h4_9]
  · linarith only [h3_4, h3_6, h3_8, h4_9]
  · linarith only [h3_4, h3_6, h3_8, h4_9]
  · linarith only [h3_8]
  · linarith only [h4_7]
  · linarith only [h3_4, h3_6, h3_8, h4_9]
  · linarith only [h4_9]

theorem pair_3_5_6 {x : Point} (hi : U3 x) (hj : U5 x) : U6 x := by
  simp only [U3] at hi
  simp only [U5] at hj
  rcases hi with ⟨h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11⟩
  rcases hj with ⟨h5_1, h5_2, h5_3, h5_4, h5_5, h5_6, h5_7, h5_8, h5_9, h5_10, h5_11⟩
  simp only [U6]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h3_1, h3_3, h3_5, h5_11]
  · linarith only [h3_3]
  · linarith only [h3_1, h3_3, h3_5, h5_11]
  · linarith only [h3_5]
  · linarith only [h3_1, h3_3, h3_5, h5_11]
  · linarith only [h3_1, h3_3, h3_5, h5_11]
  · linarith only [h3_1, h3_3, h3_5, h5_11]
  · linarith only [h3_1, h3_5, h5_1, h5_5, h5_11]
  · linarith only [h3_1, h3_3, h5_1, h5_5, h5_11]
  · linarith only [h5_11]

theorem pair_3_6_5 {x : Point} (hi : U3 x) (hj : U6 x) : U5 x := by
  simp only [U3] at hi
  simp only [U6] at hj
  rcases hi with ⟨h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11⟩
  rcases hj with ⟨h6_1, h6_2, h6_3, h6_4, h6_5, h6_6, h6_7, h6_8, h6_9, h6_10⟩
  simp only [U5]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h3_1]
  · linarith only [h3_1, h3_3, h3_5, h6_10]
  · linarith only [h3_1, h3_3, h3_5, h6_10]
  · linarith only [h3_8]
  · linarith only [h3_9]
  · linarith only [h3_1, h3_3, h3_5, h6_10]
  · linarith only [h3_1, h3_3, h3_9, h6_10]
  · linarith only [h3_1, h3_3, h3_5, h6_10]
  · linarith only [h3_1, h3_3, h3_5, h6_10]
  · linarith only [h3_1, h3_6, h3_9, h6_10]
  · linarith only [h6_10]

end FanoOdim4
