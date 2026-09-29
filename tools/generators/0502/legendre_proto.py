# 0502 prototype: M(n,k)=∫∫_{[-1,1]^2} R(|u-v|)(P_n(u)-P_n(v))P_k(u) du dv in the Legendre basis.
# K f = sum_j r_j j! (I_{-1}^{j+1} f + I_{+1}^{j+1} f); I_{-1}P_l=(P_{l+1}-P_{l-1})/(2l+1), I_{-1}P_0=P_0+P_1;
# I_{+1}^m P_n = (-1)^n reflect(I_{-1}^m P_n). ∫P_k W P_n by Adams' triple-product formula.
# Checks E(n,k)=¼√((2n+1)(2k+1)) L M against direct mpmath quadrature of ½∫∫Q(|x-y|/2)(b_n(x)-b_n(y))b_k(x).
import sys, re, time, mpmath as mp
from fractions import Fraction as F
from math import comb, factorial
mp.mp.dps=40
txt=open('../20260924_0500/ql80.lean.txt').read().replace('\n','')
q=[F(x) for x in re.findall(r'\(?(-?\d+(?:/\d+)?)\)?(?=,|\])',txt)];assert len(q)==81
L=mp.log(5)/2
ops=[0]
def Im1(c):
  out=[F(0)]*(len(c)+1)
  for l,x in enumerate(c):
    if x==0: continue
    if l==0: out[0]+=x; out[1]+=x; ops[0]+=2
    else:
      y=x/(2*l+1); out[l+1]+=y; out[l-1]-=y; ops[0]+=3
  return out
def Kop(n,r):
  a=[F(0)]*n+[F(1)]; acc={}
  for j in range(len(r)):
    a=Im1(a); jf=factorial(j)
    for l,x in enumerate(a):
      if x==0: continue
      s=x*(1+(-1)**(n+l))
      if s: acc[l]=acc.get(l,F(0))+r[j]*jf*s; ops[0]+=2
  return acc
def A(m): return F(comb(2*m,m),4**m)
def triple(l,n,k):
  s2=l+n+k
  if s2%2 or l>n+k or n>l+k or k>l+n: return F(0)
  s=s2//2; return F(2,2*s+1)*A(s-l)*A(s-n)*A(s-k)/A(s)
def M(n,k,r,W=None):
  W=W or Kop(0,r); Kn=Kop(n,r)
  first=sum(w*triple(l,n,k) for l,w in W.items())
  return first-Kn.get(k,F(0))*F(2,2*k+1)
def direct(n,k):
  bn=lambda x: mp.sqrt((2*n+1)/(2*L))*mp.legendre(n,x/L); bk=lambda x: mp.sqrt((2*k+1)/(2*L))*mp.legendre(k,x/L)
  Qf=lambda s: sum(mp.mpf(c.numerator)/c.denominator*(s/2)**j for j,c in enumerate(q))
  f=lambda x,y: mp.mpf(1)/2*Qf(abs(x-y))*(bn(x)-bn(y))*bk(x)
  return mp.quad(lambda x: mp.quad(lambda y: f(x,y),[-L,x,L]),[-L,L])
# r_j with L symbolic-free check: use high-precision rationalisation of q_j (L/2)^j
r=[F(mp.nstr(mp.mpf(c.numerator)/c.denominator*(L/2)**j,45)) for j,c in enumerate(q)]
for n,k in [(0,0),(2,2),(3,1),(6,4)]:
  ops[0]=0;t=time.time();m=M(n,k,r);e=mp.mpf(1)/4*mp.sqrt((2*n+1)*(2*k+1))*L*(mp.mpf(m.numerator)/m.denominator)
  d=direct(n,k);print(n,k,'legendre',mp.nstr(e,25),'direct',mp.nstr(d,25),'diff',mp.nstr(e-d,3),'ops',ops[0],'sec',round(time.time()-t,2))
