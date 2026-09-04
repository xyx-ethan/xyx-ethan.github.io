from pathlib import Path

p = Path("FanoLowerBound/FanoCodeRealization.lean")
s = p.read_text(encoding="utf-8")

repls = []
repls.append((
'''  rcases Bool.and_eq_true.mp habc with ⟨hab, hc⟩
  rcases Bool.and_eq_true.mp hab with ⟨ha, hb⟩
  exact ⟨⟨line, hlt⟩, ha, hb, hc⟩
''',
'''  have habc' :
      hasPoint line a = true ∧
      hasPoint line b = true ∧
      hasPoint line c = true := by
    simpa only [Bool.and_eq_true] using habc
  exact ⟨⟨line, hlt⟩, habc'⟩
'''))

insert_marker = '''private theorem fpWords_card_le_three :
'''
helper = '''private theorem nodup_of_map_nodup {α β : Type*} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs h
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hx
      exact h.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)

'''
if helper not in s:
    if insert_marker not in s:
        raise SystemExit("fpWords_card marker not found")
    s = s.replace(insert_marker, helper + insert_marker, 1)

repls.append((
'''  have hnodupFin : [i, j, k, l, m].Nodup := by
    simpa [neuronNat, List.nodup_cons, Fin.ext_iff] using hnodup
''',
'''  have hnodupFin : [i, j, k, l, m].Nodup := by
    apply nodup_of_map_nodup neuronNat
    simpa using hnodup
'''))

repls.append((
'''    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
    · exact hl
    · exact hm
''',
'''    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
'''))

repls.append((
'''  have hcardS : S.card = 5 := by
    simpa [S] using List.toFinset_card_of_nodup hnodupFin
''',
'''  have hcardS : S.card = 5 := by
    simpa [S] using toFinset_card_of_nodup hnodupFin
'''))

repls.append((
'''  fin_cases i <;> rfl
''',
'''  fin_cases i
'''))

repls.append((
'''  unfold extendLinePointsToNat
  rw [dif_pos l.isLt]
  congr
''',
'''  unfold extendLinePointsToNat
  rw [dif_pos l.isLt]
'''))

repls.append((
'''  obtain ⟨i, rfl⟩ := exists_fin_eq_of_hasPoint hp
  rw [mem_liftU_neuronNat]
  exact (mem_fanoRegion.mp hx) i
    ((hasPoint_fin_iff_mem_fanoWord l i).mp hp)
''',
'''  obtain ⟨i, hi⟩ := exists_fin_eq_of_hasPoint hp
  subst point
  rw [mem_liftU_neuronNat]
  have hiword : i ∈ fanoWord l :=
    (hasPoint_fin_iff_mem_fanoWord l i).mp hp
  exact (mem_fanoRegion.mp hx) i hiword
'''))

repls.append((
'''  have hgpP : ∀ e : Fin 4 ↪ Fin 6,
      AffineIndependent ℝ
        ((fun t : Fin 6 => P (firstSixEmb t).val) ∘ e) := by
    intro e
    simpa [P, P7, Function.comp_def] using hgp e
''',
'''  have hgpP : ∀ e : Fin 4 ↪ Fin 6,
      AffineIndependent ℝ
        ((fun t : Fin 6 => P (firstSixEmb t).val) ∘ e) := by
    intro e
    have heq :
        ((fun t : Fin 6 => P (firstSixEmb t).val) ∘ e) = p ∘ e := by
      funext x
      change extendLinePointsToNat P7 last (firstSixEmb (e x)).val = p (e x)
      rw [extendLinePointsToNat_fin]
      exact extendSixWithLast_firstSix p last (e x)
    rw [heq]
    exact hgp e
'''))

for old, new in repls:
    if old not in s:
        raise SystemExit("expected source block not found:\n" + old)
    s = s.replace(old, new, 1)

p.write_text(s, encoding="utf-8")
print("ROUND27_COMPILE_PATCH_V3_APPLIED")
