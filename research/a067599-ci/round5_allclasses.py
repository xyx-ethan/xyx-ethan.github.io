from pathlib import Path
import csv,hashlib
HERE=Path(__file__).resolve().parent
csv_path=HERE/'round5-classes.csv'
data=csv_path.read_bytes()
assert hashlib.sha256(data).hexdigest()=='bab7b4b34c95c9d5bc4a1c1361f74a35ef26847214eedfa639a467bf11f3d025'
rows=list(csv.DictReader(data.decode().splitlines()))
assert len(rows)==1126
out=['''
/-- One binary modular-exponentiation step. -/
lemma binary_mod_step (b n d m r s : ℕ)
    (h : b ^ n ≡ r [MOD m]) (hc : r ^ 2 * b ^ d ≡ s [MOD m]) :
    b ^ (n * 2 + d) ≡ s [MOD m] := by
  have h1 : (b ^ n) ^ 2 * b ^ d ≡ r ^ 2 * b ^ d [MOD m] :=
    (h.pow 2).mul_right (b ^ d)
  simpa only [pow_add, pow_mul] using h1.trans hc

''']
def power(e,mod,indent='    '):
    lines=[indent+f'have z0 : 10 ^ 0 ≡ 1 [MOD {mod}] := by decide +kernel']
    E,R=0,1
    for j,bit in enumerate(bin(e)[2:],1):
        bit=int(bit);E2=2*E+bit;R2=R*R*10**bit%mod
        lines += [indent+f'have z{j} : 10 ^ {E2} ≡ {R2} [MOD {mod}] :=',indent+f'  binary_mod_step 10 {E} {bit} {mod} {R} {R2} z{j-1} (by decide +kernel)']
        E,R=E2,R2
    return lines,f'z{j}',R
for row in rows:
    f,p,m,r=[int(row[x]) for x in ['family','prime','period','residue']]
    A,D,k,step=(740,2391,136,199)if f==1 else(370,2177,666,930)
    fam='One'if f==1 else'Two';name=f'certified_family{fam}_p{p}';mod=D*p
    out += [f'theorem {name} (t : ℕ) :\n    ¬ (residualFamily{fam} ({r} + {m} * t)).Prime := by\n',f'  have hb : {D} * {p} ∣ {A} * 10 ^ ({k} + {step} * {r}) + 1 := by\n']
    lines,z,R=power(k+step*r,mod);out += [a+'\n'for a in lines]
    out += [f'    have hz : {A} * 10 ^ {k+step*r} + 1 ≡ {A} * {R} + 1 [MOD {mod}] :=\n',f'      ({z}.mul_left {A}).add_right 1\n',f'    exact Nat.modEq_zero_iff_dvd.mp (hz.trans (by decide +kernel))\n',f'  have hp : 10 ^ ({step} * {m}) ≡ 1 [MOD {D} * {p}] := by\n']
    lines,z,R=power(step*m,mod);assert R==1
    out += [a+'\n'for a in lines]+[f'    exact {z}\n',f'  have hd : {p} ∣ residualFamily{fam} ({r} + {m} * t) :=\n',f'    dvd_residual_of_period {A} {D} {k} {step} {m} {r} {p} t hb hp\n',f'  exact not_prime_of_dvd_lt (by decide : {p} ≠ 1) hd\n',f'    (lt_of_le_of_lt (by decide : {p} ≤ 10000000)\n',f'      (tenMillion_lt_residualFamily{fam} ({r} + {m} * t)))\n\n']
    with (HERE/'CheckAxioms.lean').open('a')as fp:fp.write(f'\n#print axioms OeisA67599.{name}\n')
source=HERE/'A067599CI.lean'
source.write_text(source.read_text().replace('end OeisA67599',''.join(out)+'end OeisA67599'))
print('Generated',len(rows),'direct non-primality theorems using binary modular certificates.')
