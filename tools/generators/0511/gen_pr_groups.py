# 0511: PrRun0511_g<G>.lean: allWithin 384 (prRow n) spec_n = true, prRow n = [(prT R2 R3 R4 n k, (0,0)) | k<128]
import json, prmirror as pm
allspec={}
for G in range(8):
  L=["import PrEncl0511","",f"/-! 0511 group {G}: kernel check of Pr balls for n = {8*G}..{8*G+7} (prmirror.py). -/","",
     "open RHBall0504 RHCoarse0509 RHPrEncl0511","namespace RHPrRun0511","",
     f"def prRow{G} (n : ℕ) : List (Ball × Ball) := (List.range 128).map (fun k => (prT R2 R3 R4 n k, ((0 : ℤ), (0 : ℕ))))",""]
  for n in range(8*G,8*G+8):
    spec=[(pm.coarse(pm.prT(n,k)),(0,0)) for k in range(128)]; allspec[n]=spec
    lit='['+', '.join(f'(({a[0]}, {a[1]}), (0, 0))' for a,_ in spec)+']'
    L.append(f"def spec_{n} : List ((ℤ × ℕ) × (ℤ × ℕ)) :=\n  {lit}\n")
    L.append(f"theorem chk_{n} : allWithin 384 (prRow{G} {n}) spec_{n} = true := by\n  decide +kernel\n")
  L.append("end RHPrRun0511")
  for n in range(8*G,8*G+8): L.append(f"#print axioms RHPrRun0511.chk_{n}")
  open(f'PrRun0511_g{G}.lean','w').write('\n'.join(L)+'\n')
json.dump({str(n):v for n,v in allspec.items()},open('pr_spec_all.json','w'))
print('ok')
