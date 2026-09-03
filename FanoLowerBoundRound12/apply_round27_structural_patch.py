from pathlib import Path

p = Path("FanoLowerBound/FanoCodeRealization.lean")
s = p.read_text(encoding="utf-8")
old = '''theorem fpWords_no_five :
    ∀ w : Finset (Fin 7), w ∈ FPWords →
      ∀ i j k l m : Fin 7,
        i ∈ w → j ∈ w → k ∈ w → l ∈ w → m ∈ w →
        [i, j, k, l, m].Nodup → False := by
  decide
'''
new = '''private theorem fpWords_card_le_three :
    ∀ w : Finset (Fin 7), w ∈ FPWords → w.card ≤ 3 := by
  decide

theorem fpWords_no_five :
    ∀ w : Finset (Fin 7), w ∈ FPWords →
      ∀ i j k l m : Fin 7,
        i ∈ w → j ∈ w → k ∈ w → l ∈ w → m ∈ w →
        [i, j, k, l, m].Nodup → False := by
  intro w hw i j k l m hi hj hk hl hm hnodup
  let S : Finset (Fin 7) := [i, j, k, l, m].toFinset
  have hSsub : S ⊆ w := by
    intro x hx
    simp only [S, List.mem_toFinset, List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
    · exact hl
    · exact hm
  have hcardS : S.card = 5 := by
    simpa [S] using List.toFinset_card_of_nodup hnodup
  have h5le : 5 ≤ w.card := by
    rw [← hcardS]
    exact Finset.card_le_card hSsub
  have hle : w.card ≤ 3 := fpWords_card_le_three w hw
  omega
'''
if old not in s:
    raise SystemExit("fpWords_no_five source block not found")
p.write_text(s.replace(old, new, 1), encoding="utf-8")
print("ROUND27_STRUCTURAL_NO_FIVE_PATCH_APPLIED")
