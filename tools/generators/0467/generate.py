from pathlib import Path
from decimal import Decimal,localcontext
from math import isqrt
import json
p=Path(__file__).resolve().parent;t=Path('<DEV>/tool_trials/leancert_0455');S=10**100
with localcontext() as c:
 c.prec=140;logn=int(Decimal(3).ln()*S)
s='''import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open LeanCert.Core
namespace RHConstants0467
'''
s+=f'def log3Lo : ℚ := {logn} / {S}\ndef log3Hi : ℚ := {logn+1} / {S}\n'
s+='private def log3Interval : IntervalRat := IntervalRat.logComputable (IntervalRat.singleton 3) 260\ntheorem log3_finite : log3Lo ≤ log3Interval.lo ∧ log3Interval.hi ≤ log3Hi := by\n  decide +kernel\n'
s+='theorem log3_bounds : (log3Lo : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (log3Hi : ℝ) := by\n  have h := IntervalRat.mem_logComputable (IntervalRat.mem_singleton (3 : ℚ)) (by norm_num [IntervalRat.singleton]) 260\n  change (log3Interval.lo : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (log3Interval.hi : ℝ) at h\n  exact ⟨le_trans (by exact_mod_cast log3_finite.1) h.1, le_trans h.2 (by exact_mod_cast log3_finite.2)⟩\n'
s+='theorem log3_width : log3Hi - log3Lo = (1 : ℚ)/10^100 := by norm_num [log3Hi,log3Lo]\n'
j={'log3_lo_numerator':str(logn),'denominator':str(S),'scope':'external candidates, verify in Lean'}
for n in [2,3,5,17]:
 a=isqrt(n*S*S);j['sqrt'+str(n)]=str(a)
 s+=f'def sqrt{n}Lo : ℚ := {a} / {S}\ndef sqrt{n}Hi : ℚ := {a+1} / {S}\n'
 s+=f'theorem sqrt{n}_bounds : (sqrt{n}Lo : ℝ) ≤ Real.sqrt {n} ∧ Real.sqrt {n} ≤ (sqrt{n}Hi : ℝ) := by\n  constructor\n  · apply Real.le_sqrt_of_sq_le\n    norm_num [sqrt{n}Lo]\n  · apply (Real.sqrt_le_left (by norm_num [sqrt{n}Hi])).2\n    norm_num [sqrt{n}Hi]\n'
 s+=f'theorem sqrt{n}_width : sqrt{n}Hi - sqrt{n}Lo = (1 : ℚ)/10^100 := by norm_num [sqrt{n}Hi,sqrt{n}Lo]\n'
s+='end RHConstants0467\n'
for x in ['log3']+['sqrt'+str(n) for n in [2,3,5,17]]:
 s+=f'#print axioms RHConstants0467.{x}_bounds\n#print axioms RHConstants0467.{x}_width\n'
(p/'Constants0467.lean').write_text(s);(t/'Constants0467.lean').write_text(s);(p/'candidate.json').write_text(json.dumps(j,indent=2)+'\n')
