# 0511 v2: PrRun2_0511_g<G>.lean (n = 4G..4G+3): A-vector literals (hA_n by decide) + structural row check chk_n.
import json, prmirror as pm
def blit(bs): return '['+', '.join(f'({m}, {e})' for m,e in bs)+']'
allspec={}
for G in range(16):
  L=["import PrRow0511","",f"/-! 0511 v2 group {G}: Pr kernel checks for n = {4*G}..{4*G+3}; A vectors as checked literals. -/","",
     "open RHBall0504 RHCoarse0509 RHPrEncl0511 RHPrRow0511","namespace RHPrRun2_0511",""]
  for n in range(4*G,4*G+4):
    A={m:pm.R[m][0][n] for m in (2,3,4)}
    for m in (2,3,4): L.append(f"def a{m}_{n} : List Ball := {blit(A[m])}\n")
    L.append(f"theorem hA_{n} : R2.1.getD {n} [] = a2_{n} ∧ R3.1.getD {n} [] = a3_{n} ∧ R4.1.getD {n} [] = a4_{n} := by\n  decide +kernel\n")
    spec=[(pm.coarse(pm.prT(n,k)),(0,0)) for k in range(128)]; allspec[n]=spec
    L.append(f"def spec_{n} : List ((ℤ × ℕ) × (ℤ × ℕ)) :=\n  ["+', '.join(f'(({a[0]}, {a[1]}), (0, 0))' for a,_ in spec)+"]\n")
    L.append(f"theorem chk_{n} : allWithin 384 (rowFrom a2_{n} a3_{n} a4_{n} R2.2.2 R3.2.2 R4.2.2 R2.2.1 R3.2.1 R4.2.1) spec_{n} = true := by\n  decide +kernel\n")
  L.append("end RHPrRun2_0511")
  for n in range(4*G,4*G+4): L.append(f"#print axioms RHPrRun2_0511.hA_{n}\n#print axioms RHPrRun2_0511.chk_{n}")
  open(f'PrRun2_0511_g{G}.lean','w').write('\n'.join(L)+'\n')
json.dump({str(n):v for n,v in allspec.items()},open('pr_spec_all.json','w'))
print('ok')
