from pathlib import Path
import csv,hashlib
HERE=Path(__file__).resolve().parent
data=(HERE/'round5-classes.csv').read_bytes()
assert hashlib.sha256(data).hexdigest()=='bab7b4b34c95c9d5bc4a1c1361f74a35ef26847214eedfa639a467bf11f3d025'
rows=list(csv.DictReader(data.decode().splitlines()))
assert len(rows)==1126
out=['''
/-- Binary exponentiation with an explicit small exponent-equality certificate. -/
lemma binary_mod_step_safe (b n d m r s N : ℕ)
    (hN : n * 2 + d = N)
    (h : b ^ n ≡ r [MOD m]) (hc : r ^ 2 * b ^ d ≡ s [MOD m]) :
    b ^ N ≡ s [MOD m] := by
  subst N
  have h1 : (b ^ n) ^ 2 * b ^ d ≡ r ^ 2 * b ^ d [MOD m] :=
    (h.pow 2).mul_right (b ^ d)
  simpa only [pow_add, pow_mul] using h1.trans hc

/-- Transport numeral exponents only while all large powers remain symbolic. -/
lemma dvd_residual_of_certificates
    (A D Q0 M m r p k E F H R : ℕ)
    (hE : Q0 + M * r = E) (hF : M * m = F) (hH : D * p = H)
    (hb : 10 ^ E ≡ R [MOD H]) (hz : A * R + 1 ≡ 0 [MOD H])
    (hp : 10 ^ F ≡ 1 [MOD H]) :
    p ∣ (A * 10 ^ (Q0 + M * (r + m * k)) + 1) / D := by
  apply dvd_residual_of_period A D Q0 M m r p k
  · rw [hE, hH]
    have h0 : A * 10 ^ E + 1 ≡ 0 [MOD H] :=
      ((hb.mul_left A).add_right 1).trans hz
    exact Nat.modEq_zero_iff_dvd.mp h0
  · rw [hF, hH]
    exact hp

''']
def power(e,mod):
    lines=[f'    have z0 : 10 ^ 0 ≡ 1 [MOD {mod}] := by decide +kernel']
    E,R=0,1
    for j,bit in enumerate(bin(e)[2:],1):
        bit=int(bit);E2=2*E+bit;R2=R*R*10**bit%mod
        lines += [f'    have z{j} : 10 ^ {E2} ≡ {R2} [MOD {mod}] :=',f'      binary_mod_step_safe 10 {E} {bit} {mod} {R} {R2} {E2}',f'        (by decide) z{j-1} (by decide +kernel)']
        E,R=E2,R2
    return '\n'.join(lines)+f'\n    exact z{j}\n',R
names=[]
for row in rows:
    f,p,m,r=[int(row[x]) for x in ['family','prime','period','residue']]
    A,D,k,step=(740,2391,136,199)if f==1 else(370,2177,666,930)
    fam='One'if f==1 else'Two';name=f'certified_family{fam}_p{p}';H=D*p;E=k+step*r;F=step*m
    base,R=power(E,H);period,R1=power(F,H);assert R1==1
    out += [f'theorem {name} (t : ℕ) :\n    ¬ (residualFamily{fam} ({r} + {m} * t)).Prime := by\n',f'  have hb : 10 ^ {E} ≡ {R} [MOD {H}] := by\n',base,f'  have hp : 10 ^ {F} ≡ 1 [MOD {H}] := by\n',period,f'  have hd : {p} ∣ residualFamily{fam} ({r} + {m} * t) :=\n',f'    dvd_residual_of_certificates {A} {D} {k} {step} {m} {r} {p} t {E} {F} {H} {R}\n',f'      (by decide) (by decide) (by decide) hb (by decide +kernel) hp\n',f'  exact not_prime_of_dvd_lt (by decide : {p} ≠ 1) hd\n',f'    (lt_of_le_of_lt (by decide : {p} ≤ 10000000)\n',f'      (tenMillion_lt_residualFamily{fam} ({r} + {m} * t)))\n\n']
    names.append(name)
source=HERE/'A067599CI.lean'
source.write_text(source.read_text().replace('end OeisA67599',''.join(out)+'end OeisA67599'))
audit=HERE/'CheckAxioms.lean'
with audit.open('a')as fp:
    for name in ['binary_mod_step_safe','dvd_residual_of_certificates']+names:
        fp.write('\n#print axioms OeisA67599.'+name+'\n')
print('Generated',len(rows),'non-primality certificates with symbolic transport.')
