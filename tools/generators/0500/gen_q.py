# 0500: exact Taylor coefficients (in t) of Rk(2t), Rk(s)=exp(s/2)/sinh s - 1/s, degree NQ. Emits Lean list.
import sys
from fractions import Fraction as F
from math import factorial
NQ=int(sys.argv[1]) if len(sys.argv)>1 else 80
M=NQ+10
sh=[F(0) if k%2==0 else F(1,factorial(k)) for k in range(M)]
ch=[F(1,factorial(k)) if k%2==0 else F(0) for k in range(M)]
def mul(p,q):
  r=[F(0)]*(len(p)+len(q)-1)
  for i,x in enumerate(p):
    for j,y in enumerate(q): r[i+j]+=x*y
  return r
shch=mul(sh,ch)[:M]
N=[F(0)]*M
for k in range(M-1): N[k+1]+=ch[k]+sh[k]
for k in range(M): N[k]-=shch[k]
D=[F(0)]+[2*x for x in shch[:M-1]]
nn=N[2:];dd=D[2:];q=[]
for k in range(NQ+1): q.append((nn[k]-sum(q[i]*dd[k-i] for i in range(k)))/dd[0])
def lit(x): return '0' if x==0 else (f'({x.numerator})' if x.denominator==1 else f'({x.numerator}/{x.denominator})')
print('def ql : List ℚ := [' + ',\n  '.join(lit(x) for x in q) + ']')
