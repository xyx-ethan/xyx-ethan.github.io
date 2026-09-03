import FanoCertificate.Core

namespace FanoOdim4

theorem pair_3_7_4 {x : Point} (hi : U3 x) (hj : U7 x) : U4 x := by
  simp only [U3] at hi
  simp only [U7] at hj
  rcases hi with ⟨h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11⟩
  rcases hj with ⟨h7_1, h7_2, h7_3, h7_4, h7_5, h7_6, h7_7, h7_8, h7_9, h7_10, h7_11⟩
  simp only [U4]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h3_4, h3_6, h7_9, h7_11]
  · linarith only [h3_4, h3_6, h3_8, h7_9]
  · linarith only [h3_4, h3_6, h7_9, h7_11]
  · linarith only [h3_4, h3_6, h3_8, h7_9]
  · linarith only [h3_4, h3_6, h7_9, h7_11]
  · linarith only [h3_6]
  · linarith only [h7_9]
  · linarith only [h3_4, h3_6, h3_8, h7_11]
  · linarith only [h7_11]
  · linarith only [h3_4, h3_6, h3_8, h7_11]

theorem pair_4_5_1 {x : Point} (hi : U4 x) (hj : U5 x) : U1 x := by
  simp only [U4] at hi
  simp only [U5] at hj
  rcases hi with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  rcases hj with ⟨h5_1, h5_2, h5_3, h5_4, h5_5, h5_6, h5_7, h5_8, h5_9, h5_10, h5_11⟩
  simp only [U1]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4_1, h4_10, h5_4, h5_7]
  · linarith only [h4_1, h4_10, h5_4, h5_7]
  · linarith only [h4_1]
  · linarith only [h4_1, h4_8, h4_10]
  · linarith only [h5_4]
  · linarith only [h4_1, h4_8, h4_10, h5_7]
  · linarith only [h5_7]
  · linarith only [h4_1, h4_8, h4_10, h5_7]
  · linarith only [h4_1, h4_8, h4_10, h5_7]

theorem pair_4_6_2 {x : Point} (hi : U4 x) (hj : U6 x) : U2 x := by
  simp only [U4] at hi
  simp only [U6] at hj
  rcases hi with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  rcases hj with ⟨h6_1, h6_2, h6_3, h6_4, h6_5, h6_6, h6_7, h6_8, h6_9, h6_10⟩
  simp only [U2]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4_2]
  · linarith only [h4_2, h4_3, h4_5, h6_9]
  · linarith only [h4_4]
  · linarith only [h4_2, h4_3, h4_5, h6_9]
  · linarith only [h4_2, h4_3, h4_4, h6_9]
  · linarith only [h4_2, h4_3, h4_4, h6_9]
  · linarith only [h4_2, h4_3, h4_4, h6_9]
  · linarith only [h6_9]
  · linarith only [h4_2, h4_3, h4_4, h6_9]
  · linarith only [h4_2, h4_3, h4_5, h6_9]

theorem pair_4_7_3 {x : Point} (hi : U4 x) (hj : U7 x) : U3 x := by
  simp only [U4] at hi
  simp only [U7] at hj
  rcases hi with ⟨h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7, h4_8, h4_9, h4_10⟩
  rcases hj with ⟨h7_1, h7_2, h7_3, h7_4, h7_5, h7_6, h7_7, h7_8, h7_9, h7_10, h7_11⟩
  simp only [U3]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h4_6, h4_7, h7_3, h7_8]
  · linarith only [h4_6, h4_7, h4_9, h7_3]
  · linarith only [h4_6, h4_7, h4_9, h7_3]
  · linarith only [h7_3]
  · linarith only [h4_6, h4_7, h4_9, h7_3]
  · linarith only [h4_6]
  · linarith only [h4_6, h4_9, h7_3, h7_8]
  · linarith only [h7_8]
  · linarith only [h4_6, h4_7, h4_9, h7_3]
  · linarith only [h4_6, h4_9, h7_3, h7_8]
  · linarith only [h4_6, h4_9, h7_3, h7_8]

theorem pair_5_6_3 {x : Point} (hi : U5 x) (hj : U6 x) : U3 x := by
  simp only [U5] at hi
  simp only [U6] at hj
  rcases hi with ⟨h5_1, h5_2, h5_3, h5_4, h5_5, h5_6, h5_7, h5_8, h5_9, h5_10, h5_11⟩
  rcases hj with ⟨h6_1, h6_2, h6_3, h6_4, h6_5, h6_6, h6_7, h6_8, h6_9, h6_10⟩
  simp only [U3]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h5_1]
  · linarith only [h5_1, h5_11, h6_2, h6_4]
  · linarith only [h6_2]
  · linarith only [h5_1, h5_5, h5_11, h6_2]
  · linarith only [h6_4]
  · linarith only [h5_1, h5_11, h6_2, h6_4]
  · linarith only [h5_1, h5_11, h6_2, h6_4]
  · linarith only [h5_1, h5_5, h5_11, h6_2]
  · linarith only [h5_5]
  · linarith only [h5_1, h5_5, h5_11, h6_2]
  · linarith only [h5_1, h5_5, h5_11, h6_2]

theorem pair_5_7_2 {x : Point} (hi : U5 x) (hj : U7 x) : U2 x := by
  simp only [U5] at hi
  simp only [U7] at hj
  rcases hi with ⟨h5_1, h5_2, h5_3, h5_4, h5_5, h5_6, h5_7, h5_8, h5_9, h5_10, h5_11⟩
  rcases hj with ⟨h7_1, h7_2, h7_3, h7_4, h7_5, h7_6, h7_7, h7_8, h7_9, h7_10, h7_11⟩
  simp only [U2]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h5_2, h5_10, h7_4, h7_5]
  · linarith only [h7_4]
  · linarith only [h5_2, h5_10, h7_4, h7_5]
  · linarith only [h7_5]
  · linarith only [h5_6]
  · linarith only [h5_2, h5_3, h5_10, h7_4]
  · linarith only [h5_2, h5_3, h5_10, h7_4]
  · linarith only [h5_2, h5_3, h5_10, h7_4]
  · linarith only [h5_10]
  · linarith only [h5_2, h5_3, h5_10, h7_4]

theorem pair_6_7_1 {x : Point} (hi : U6 x) (hj : U7 x) : U1 x := by
  simp only [U6] at hi
  simp only [U7] at hj
  rcases hi with ⟨h6_1, h6_2, h6_3, h6_4, h6_5, h6_6, h6_7, h6_8, h6_9, h6_10⟩
  rcases hj with ⟨h7_1, h7_2, h7_3, h7_4, h7_5, h7_6, h7_7, h7_8, h7_9, h7_10, h7_11⟩
  simp only [U1]
  dsimp only [L] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h6_6, h6_7, h6_8, h7_1]
  · linarith only [h7_1]
  · linarith only [h6_6, h6_7, h6_8, h7_1]
  · linarith only [h6_6, h6_7, h6_8, h7_1]
  · linarith only [h6_5, h6_7, h6_8, h7_1]
  · linarith only [h6_6]
  · linarith only [h6_5, h6_7, h6_8, h7_1]
  · linarith only [h6_8]
  · linarith only [h6_5, h6_7, h6_8, h7_1]

end FanoOdim4
