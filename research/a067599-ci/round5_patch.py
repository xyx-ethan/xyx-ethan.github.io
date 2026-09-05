from pathlib import Path
import re
root = Path(__file__).resolve().parent
p = root / 'A067599CI.lean'
s = p.read_text()
generic = '''/-- A quotient bound before substituting any large exponent. -/
lemma residual_quotient_lower (A D e c h : ℕ) (hD : 0 < D)
    (he : h ≤ e) (hc : (c + 1) * D ≤ A * 10 ^ h + 1) :
    c < (A * 10 ^ e + 1) / D := by
  have hp : 10 ^ h ≤ 10 ^ e :=
    Nat.pow_le_pow_right (by decide : 0 < 10) he
  have hn : (c + 1) * D ≤ A * 10 ^ e + 1 :=
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left A hp) 1)
  have hq : c + 1 ≤ (A * 10 ^ e + 1) / D :=
    (Nat.le_div_iff_mul_le hD).2 hn
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hq

'''
pos = s.index('/-- Every term in the first residual family is larger')
s = s[:pos] + generic + s[pos:]
for name,fam,c,A,D,e in [('twoHundredEleven','One',211,740,2391,'136 + 199 * t'),('oneFiftySeven','Two',157,370,2177,'666 + 930 * t')]:
    pat = rf'theorem {name}_lt_residualFamily{fam} \(t : ℕ\) :.*?(?=\n\n)'
    new = f'''theorem {name}_lt_residualFamily{fam} (t : ℕ) :
    {c} < residualFamily{fam} t := by
  exact residual_quotient_lower {A} {D} ({e}) {c} 3
    (by decide) (by omega) (by decide)'''
    s,count = re.subn(pat,new,s,flags=re.S)
    assert count == 1
extra = '''
/-- A finite covering by proper divisors excludes prime values. -/
theorem not_prime_of_finite_cover
    (q : ℕ → ℕ) (K : ℕ) (m r d : Fin K → ℕ)
    (cover : ∀ t, ∃ j, t % m j = r j)
    (factors : ∀ j t, t % m j = r j → d j ∣ q t)
    (proper : ∀ j t, t % m j = r j → 1 < d j ∧ d j < q t) :
    ∀ t, ¬ (q t).Prime := by
  intro t
  obtain ⟨j, hj⟩ := cover t
  obtain ⟨hlo, hhi⟩ := proper j t hj
  exact not_prime_of_dvd_lt (by omega) (factors j t hj) hhi

'''
for fam,A,D,k,step in [('One',740,2391,136,199),('Two',370,2177,666,930)]:
    extra += f'''theorem tenMillion_lt_residualFamily{fam} (t : ℕ) :
    10000000 < residualFamily{fam} t := by
  exact residual_quotient_lower {A} {D} ({k} + {step} * t) 10000000 8
    (by decide) (by omega) (by decide)

'''
for fam,A,D,k,step,p0,m,r in [('One',740,2391,136,199,797,797,529),('Two',370,2177,666,930,7,7,5),('Two',370,2177,666,930,311,311,93)]:
    extra += f'''theorem denominator_{p0}_dvd_family{fam} (k : ℕ) :
    {p0} ∣ residualFamily{fam} ({r} + {m} * k) := by
  simpa only [residualFamily{fam}] using
    dvd_residual_of_period {A} {D} {k} {step} {m} {r} {p0} k
      (by decide +kernel) (by decide +kernel)

theorem denominator_{p0}_family{fam}_not_prime (k : ℕ) :
    ¬ (residualFamily{fam} ({r} + {m} * k)).Prime := by
  exact not_prime_of_dvd_lt (by decide)
    (denominator_{p0}_dvd_family{fam} k)
    (lt_of_le_of_lt (by decide : {p0} ≤ 10000000)
      (tenMillion_lt_residualFamily{fam} ({r} + {m} * k)))

'''
s = s.replace('end OeisA67599',extra + 'end OeisA67599')
p.write_text(s)
a = root / 'CheckAxioms.lean'
text = a.read_text()
for name in ['residual_quotient_lower','not_prime_of_finite_cover','tenMillion_lt_residualFamilyOne','tenMillion_lt_residualFamilyTwo','denominator_797_familyOne_not_prime','denominator_7_familyTwo_not_prime','denominator_311_familyTwo_not_prime']:
    text += '\n#print axioms OeisA67599.' + name + '\n'
a.write_text(text)
