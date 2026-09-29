# 0507: generate RpBall0507_g<G>.lean (n = 8G..8G+7): (run (2^512) n rq 81).2.2 = <list> by decide +kernel
import sys, json
sys.path.insert(0,'../20260924_0505')
import mirror
S=2**512
data={}
for G in range(8):
  lines=["import AlgoBall0505","import Entry22_0505","",
    f"/-! 0507 group {G}: kernel ball vectors `(run (2^512) n rq 81).2.2` for n = {8*G}..{8*G+7} (mirror.py). -/","",
    "open RHBall0504 RHBallVec0504 RHAlgoBall0505","namespace RHRpBall0507",""]
  for n in range(8*G,8*G+8):
    acc=mirror.run(S,n,81); data[n]=acc
    lit='['+', '.join(f'({m}, {e})' for m,e in acc)+']'
    lines.append(f"theorem acc_{n} : (run (2 ^ 512) {n} RHEntry22_0505.rq 81).2.2 =\n    {lit} := by\n  decide +kernel\n")
  lines.append("end RHRpBall0507")
  for n in range(8*G,8*G+8): lines.append(f"#print axioms RHRpBall0507.acc_{n}")
  open(f'RpBall0507_g{G}.lean','w').write('\n'.join(lines)+'\n')
json.dump({str(n):[[m,e] for m,e in v] for n,v in data.items()},open('acc_all.json','w'))
print('ok')
