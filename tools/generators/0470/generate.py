from pathlib import Path
from fractions import Fraction as F
import re,json
R=Path(__file__).resolve().parent
T=Path('<DEV>/tool_trials/leancert_0455')
D=10**100
s=['import PrimeAPI0470','set_option maxRecDepth 100000','set_option maxHeartbeats 10000000','open LeanCert.Core','namespace RHPrimeNumeric0470']
V={}; names=[]
def put(txt):
 s.append(txt)
 names.extend(re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',txt,re.M))
def iv(n,lo,hi):
 V[n]=(lo,hi)
 put(f'def {n}I : IntervalRat := ⟨{lo.numerator} / {lo.denominator}, {hi.numerator} / {hi.denominator}, by decide +kernel⟩')
for n,f,lo,hi,e,th in [('l2','Log2_100','Trial0455.lo','Trial0455.hi','Real.log 2','Trial0455.log2_bounds'),('l3','Constants0467','RHConstants0467.log3Lo','RHConstants0467.log3Hi','Real.log 3','RHConstants0467.log3_bounds')]+[(f's{k}','Constants0467',f'RHConstants0467.sqrt{k}Lo',f'RHConstants0467.sqrt{k}Hi',f'Real.sqrt {k}',f'RHConstants0467.sqrt{k}_bounds') for k in [2,3,17]]:
 txt=(T/(f+'.lean')).read_text()
 vals=[]
 for v in [lo,hi]:
  m=re.search(r'def '+v.split('.')[-1]+r' : ℚ := (\d+) / (\d+)',txt);vals.append(F(int(m[1]),int(m[2])))
 V[n]=tuple(vals)
 put(f'def {n}I : IntervalRat := ⟨{lo}, {hi}, by decide +kernel⟩')
 put(f'noncomputable def {n}Expr : ℝ := {e}')
 put(f'theorem {n}_mem : {n}Expr ∈ {n}I := by\n  exact {th}')
for n,k in [('one',1),('four',4),('seventeen',17),('thirtyfour',34)]:
 iv(n,F(k),F(k));put(f'noncomputable def {n}Expr : ℝ := {k}')
 put(f'theorem {n}_mem : {n}Expr ∈ {n}I := by norm_num [{n}Expr, {n}I, IntervalRat.mem_def]')
def op(n,typ,a,b):
 al,ah=V[a];bl,bh=V[b]
 if typ=='add': v=(al+bl,ah+bh);symbol='+';raw=f'IntervalRat.add {a}I {b}I'; proof=f'IntervalRat.mem_add {a}_mem {b}_mem'
 if typ=='sub': v=(al-bh,ah-bl);symbol='-';raw=f'IntervalRat.sub {a}I {b}I';proof=f'IntervalRat.mem_sub {a}_mem {b}_mem'
 if typ=='mul': z=[x*y for x in [al,ah] for y in [bl,bh]];v=(min(z),max(z));symbol='*';raw=f'IntervalRat.mul {a}I {b}I';proof=f'IntervalRat.mem_mul {a}_mem {b}_mem'
 if typ=='div':
  assert bl>0
  z=[x/y for x in [al,ah] for y in [bl,bh]];v=(min(z),max(z));symbol='/'
  put(f'theorem {n}_den_lo_pos : 0 < {b}I.lo := by decide +kernel')
  put(f'theorem {n}_den_pos : 0 < {b}Expr := positive_of_mem {n}_den_lo_pos {b}_mem')
  raw=f'posDiv {a}I {b}I {n}_den_lo_pos';proof=f'mem_posDiv {n}_den_lo_pos {a}_mem {b}_mem'
 lo=F((v[0]*D).__floor__(),D);hi=F((v[1]*D).__ceil__(),D)
 iv(n,lo,hi)
 put(f'noncomputable def {n}Expr : ℝ := {a}Expr {symbol} {b}Expr')
 put(f'theorem {n}_finite : {n}I.lo ≤ ({raw}).lo ∧ ({raw}).hi ≤ {n}I.hi := by\n  decide +kernel')
 put(f'theorem {n}_mem : {n}Expr ∈ {n}I := widen {n}_finite ({proof})')
for t in [('alpha','div','l2','s2'),('splus','add','one','s17'),('lprod','mul','l2','splus'),('lam','div','lprod','four'),('sdiff','sub','seventeen','s17'),('p','div','sdiff','thirtyfour'),('delta','sub','lam','alpha'),('mu','div','l3','s3'),('pmu','mul','p','mu'),('dmu','add','delta','mu'),('denominator','add','dmu','pmu'),('pdelta','mul','p','delta'),('numerator','mul','pdelta','mu'),('gamma','div','numerator','denominator'),('sum','add','lam','mu'),('prime','sub','sum','gamma')]: op(*t)
lo,hi=V['prime']
put(f'def primeLo : ℚ := {lo.numerator} / {lo.denominator}')
put(f'def primeHi : ℚ := {hi.numerator} / {hi.denominator}')
put('theorem prime_bounds : (primeLo : ℝ) ≤ primeExpr ∧ primeExpr ≤ (primeHi : ℝ) := prime_mem')
put('theorem prime_width : primeHi - primeLo ≤ (1 : ℚ) / 10^95 := by decide +kernel')
put('theorem denominator_pos : 0 < deltaExpr + muExpr + pExpr * muExpr := gamma_den_pos')
s.append('end RHPrimeNumeric0470')
s.extend('#print axioms RHPrimeNumeric0470.'+n for n in names)
text='\n\n'.join(s)+'\n'
(T/'PrimeNumeric0470.lean').write_text(text)
R.joinpath('PrimeNumeric0470.lean').write_text(text)
R.joinpath('candidate_endpoints.json').write_text(json.dumps({n:[str(l),str(h)] for n,(l,h) in V.items()},indent=2))
print('width',float(hi-lo),'prime',float(lo),'declarations',len(names))
