# 0505: exact Python mirror of the Lean ball algorithm (RHAlgoBall0505.run); also emits Lean rq literal.
import sys, re, mpmath as mp
from math import factorial
from fractions import Fraction as F
mp.mp.dps=80
txt=open('../20260924_0500/ql80.lean.txt').read().replace('\n','')
q=[F(x) for x in re.findall(r'\(?(-?\d+(?:/\d+)?)\)?(?=,|\])',txt)];assert len(q)==81
L=mp.log(5)/2
D=10**60
rq=[(int(mp.nint(mp.mpf(c.numerator)/c.denominator*(L/2)**j*D)),D) for j,c in enumerate(q)]
def smul(a,d,b): return (b[0]*a//d, (b[1]*abs(a)+d-1)//d+1)
def add(b,c): return (b[0]+c[0],b[1]+c[1])
def sub(b,c): return (b[0]-c[0],b[1]+c[1])
def neg(b): return (-b[0],b[1])
Z=(0,0)
def zipP(f,a,b):
  n=max(len(a),len(b)); return [f(a[i] if i<len(a) else Z, b[i] if i<len(b) else Z) for i in range(n)]
def vIm(bs):
  A=[smul(1,2*l+1,b) for l,b in enumerate(bs)]
  return zipP(sub,[A[0] if A else Z]+A,A[1:])
def vX(bs):
  B=[smul(l+1,2*l+1,b) for l,b in enumerate(bs)]; C=[smul(l,2*l+1,b) for l,b in enumerate(bs)]
  return zipP(add,[Z]+B,C[1:])
def vrefl(bs): return [b if l%2==0 else neg(b) for l,b in enumerate(bs)]
def sym(n,bs): r=vrefl(bs); return zipP(add,bs, r if n%2==0 else [neg(x) for x in r])
def run(S,n,J):
  a=[Z]*n+[(S,0)]; b=list(a); acc=[]
  for j in range(J):
    a=vIm(a); b=zipP(add,b,vX(b)); num,den=rq[j]
    t=zipP(sub,[smul(num,den*(j+1),x) for x in sym(n,b)],[smul(num*factorial(j),den,x) for x in sym(n,a)])
    acc=zipP(add,acc,t)
  return acc
if __name__=='__main__':
  if sys.argv[1]=='lean':
    print('def rq : List (ℤ × ℕ) := [' + ',\n  '.join(f'({a}, {d})' for a,d in rq)+']')
  else:
    n,k=int(sys.argv[2]),int(sys.argv[3]); S=2**512
    acc=run(S,n,81); m,e=acc[k]
    print(n,k,'m=',m,'e=',e)
    g=mp.mpf(m)/S; M=2*g/(2*k+1); E=mp.mpf(1)/4*mp.sqrt((2*n+1)*(2*k+1))*L*M
    print('gamma',mp.nstr(g,30),'radius',mp.nstr(mp.mpf(e)/S,3),'Rp-exactpart',mp.nstr(E,30))
