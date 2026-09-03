from pathlib import Path

p = Path('FanoLowerBound/GeneralPositionSelection.lean')
s = p.read_text(encoding='utf-8')
marker = '/-- Every embedding `Fin 4 ↪ Fin 6` is a permutation of exactly one increasing canonical embedding. -/'
lemma = r'''/-- The fifteen strictly increasing quadruples in `Fin 6`, kernel-reduced by `decide`. -/
private theorem increasing_fin6_quadruple_cases :
    ∀ a b c d : Fin 6, a < b → b < c → c < d →
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 2 ∧ d.val = 3) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 2 ∧ d.val = 4) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 2 ∧ d.val = 5) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 3 ∧ d.val = 4) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 3 ∧ d.val = 5) ∨
      (a.val = 0 ∧ b.val = 1 ∧ c.val = 4 ∧ d.val = 5) ∨
      (a.val = 0 ∧ b.val = 2 ∧ c.val = 3 ∧ d.val = 4) ∨
      (a.val = 0 ∧ b.val = 2 ∧ c.val = 3 ∧ d.val = 5) ∨
      (a.val = 0 ∧ b.val = 2 ∧ c.val = 4 ∧ d.val = 5) ∨
      (a.val = 0 ∧ b.val = 3 ∧ c.val = 4 ∧ d.val = 5) ∨
      (a.val = 1 ∧ b.val = 2 ∧ c.val = 3 ∧ d.val = 4) ∨
      (a.val = 1 ∧ b.val = 2 ∧ c.val = 3 ∧ d.val = 5) ∨
      (a.val = 1 ∧ b.val = 2 ∧ c.val = 4 ∧ d.val = 5) ∨
      (a.val = 1 ∧ b.val = 3 ∧ c.val = 4 ∧ d.val = 5) ∨
      (a.val = 2 ∧ b.val = 3 ∧ c.val = 4 ∧ d.val = 5) := by
  decide

'''
if 'private theorem increasing_fin6_quadruple_cases' not in s:
    s = s.replace(marker, lemma + marker, 1)
start = s.index('  have hclass :\n', s.index('theorem every_fin4_emb_fin6_factors'))
end = s.index('  rcases hclass with', start)
block = s[start:end]
needle = ':= by\n    omega\n'
if needle not in block:
    raise SystemExit('expected omega classification block not found')
block = block.replace(needle, ':=\n    increasing_fin6_quadruple_cases _ _ _ _ h01 h12 h23\n', 1)
s = s[:start] + block + s[end:]
p.write_text(s, encoding='utf-8')
print('ROUND26_FAST_PATCH_APPLIED')
