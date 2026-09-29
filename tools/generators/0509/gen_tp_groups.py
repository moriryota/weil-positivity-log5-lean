# 0509: TpRun0509_g<G>.lean: allWithin 384 (tpRun (2^512) n 82 gq 128) spec_n = true (coarse 2^128 balls)
import json, tmirror
S=2**512; SH=384; W=tmirror.Wb(S)
def coarse(b):
  m,e=b; c=(m+(1<<(SH-1)))>>SH; r=-(-(e+abs(m-(c<<SH)))>>SH)
  assert abs(m-(c<<SH))+e <= r<<SH
  return (c,r)
allspec={}
for G in range(8):
  L=["import TpEncl0509","",f"/-! 0509 group {G}: kernel check of Tp balls for n = {8*G}..{8*G+7} against coarse (2^128) specs (tmirror.py). -/","",
     "open RHBall0504 RHCoarse0509 RHTpBall0509","namespace RHTpRun0509",""]
  for n in range(8*G,8*G+8):
    out=tmirror.tpRun(S,n,128,W)
    spec=[(coarse(a),coarse(b)) for a,b in out]; allspec[n]=spec
    lit='['+', '.join(f'(({a[0]}, {a[1]}), ({b[0]}, {b[1]}))' for a,b in spec)+']'
    L.append(f"def spec_{n} : List ((ℤ × ℕ) × (ℤ × ℕ)) :=\n  {lit}\n")
    L.append(f"theorem chk_{n} : allWithin 384 (tpRun (2 ^ 512) {n} 82 RHTpEncl0509.gq 128) spec_{n} = true := by\n  decide +kernel\n")
  L.append("end RHTpRun0509")
  for n in range(8*G,8*G+8): L.append(f"#print axioms RHTpRun0509.chk_{n}")
  open(f'TpRun0509_g{G}.lean','w').write('\n'.join(L)+'\n')
json.dump({str(n):v for n,v in allspec.items()},open('tp_spec_all.json','w'))
print('ok')
