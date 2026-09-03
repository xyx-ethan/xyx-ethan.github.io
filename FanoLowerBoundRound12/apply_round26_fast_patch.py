from pathlib import Path

p = Path('FanoLowerBound/GeneralPositionSelection.lean')
s = p.read_text(encoding='utf-8')

# `ext` for embeddings reduces the goal to equality of the underlying `Fin.val`s.
s = s.replace(
    "  ext i\n  have hi := h (σ.symm i)\n  simpa using hi\n",
    "  ext i\n  have hi := h (σ.symm i)\n  have hi' : e i = q (σ.symm i) := by simpa using hi\n  exact congrArg Fin.val hi'\n",
    1,
)

marker = '/-- Every embedding `Fin 4 ↪ Fin 6` is a permutation of exactly one increasing canonical embedding. -/'
lemma = r'''/-- The fifteen strictly increasing quadruples in `Fin 6`, reduced by finite cases. -/
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
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

'''
if 'private theorem increasing_fin6_quadruple_cases' not in s:
    s = s.replace(marker, lemma + marker, 1)
else:
    start_lemma = s.index('/-- The fifteen strictly increasing quadruples')
    end_lemma = s.index(marker, start_lemma)
    s = s[:start_lemma] + lemma + s[end_lemma:]

start = s.index('  have hclass :\n', s.index('theorem every_fin4_emb_fin6_factors'))
end = s.index('  rcases hclass with', start)
block = s[start:end]
needle_omega = ':= by\n    omega\n'
needle_call = ':=\n    increasing_fin6_quadruple_cases _ _ _ _ h01 h12 h23\n'
if needle_omega in block:
    block = block.replace(needle_omega, needle_call, 1)
elif needle_call not in block:
    raise SystemExit('expected classification proof not found')
s = s[:start] + block + s[end:]

p.write_text(s, encoding='utf-8')
print('ROUND26_FAST_PATCH_APPLIED')
