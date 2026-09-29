# 0512: exact Python mirror of RHEntryBall0512.entryB and the Mq ball stages (scale 2^128).
import json, re, sys
from fractions import Fraction as F
sys.path.insert(0,'../20260925_0509'); sys.path.insert(0,'../20260924_0505')
from mirror import smul, add, sub, neg, Z
from tmirror import mulB as mulB_
S=2**128
mulB=lambda a,b: mulB_(S,a,b)
C=json.load(open('consts.json'))
LB=tuple(C['L']); h0B=tuple(C['h0']); CdB=tuple(C['Cd']); cT=[tuple(x) for x in C['c']]
R='../'
rpS={int(k):v for k,v in {}.items()}
acc=json.load(open(R+'20260925_0507/acc_all.json'))
SH=384
def coarse(b):
  m,e=b; c=(m+(1<<(SH-1)))>>SH; r=-(-(e+abs(m-(c<<SH)))>>SH); return (c,r)
def rpB(n,k):
  v=acc[str(n)]; return coarse(v[k]) if k<len(v) else (0,0)
tps=json.load(open(R+'20260925_0509/tp_spec_all.json')); prs=json.load(open(R+'20260925_0511/pr_spec_all.json'))
tpB=lambda n,k: tuple(tps[str(n)][k][1]); prB=lambda n,k: tuple(prs[str(n)][k][0])
ccs=open(R+'20260925_0510/ccspec.txt').read()
ccl=[tuple(map(int,t)) for t in re.findall(r'\(\((-?\d+), (\d+)\), \((-?\d+), (\d+)\)\)',ccs)]
def ceB(n,odd):
  if n<40:
    c=ccl[n] if n<len(ccl) else (0,0,0,0)
    return (c[2],c[3]) if odd else (c[0],c[1])
  return (0,0)
def floorq(q): return q.numerator//q.denominator
def qBall(q): return (floorq(q*S),1)
H=[F(0)]
for i in range(1,200): H.append(H[-1]+F(1,i))
def cB(n): return cT[n] if n<len(cT) else (0,0)
def hypB(n,odd): return mulB(mulB(LB,cB(n)), add(ceB(n,odd),(0,1)))
eR=1400000000000000; eT=700000000000000
def sgn(n,k): return 1 if (n+k)%2==0 else 0
def entryB(n,k):
  cc2=mulB(cB(n),cB(k)); FR=smul(1,2*k+1,mulB(mulB(LB,LB),cc2)); FT=mulB(LB,cc2)
  diag=add(add(h0B,qBall(H[n])),CdB) if n==k else (0,0)
  rpart=add(mulB(FR,rpB(n,k)),(0,eR))
  tpart=add(neg(smul(sgn(n,k),1,mulB(FT,tpB(n,k)))),(0,eT))
  ccp=smul(2,1,mulB(hypB(n,False),hypB(k,False)))
  ssp=smul(2,1,mulB(hypB(n,True),hypB(k,True)))
  prp=smul(2*sgn(n,k),1,mulB(FT,prB(n,k)))
  return sub(add(add(add(diag,rpart),tpart),ccp),add(ssp,prp))
if __name__=='__main__':
  import mpmath as mp
  b=entryB(0,0); print(mp.nstr(mp.mpf(b[0])/S,25), b[1]/S)
  b=entryB(2,2); print(mp.nstr(mp.mpf(b[0])/S,25), b[1]/S)

src=open('<DEV>/tool_trials/rh_trunc_0500/FixedCoordinates.lean').read()
def parse(name, two):
  seg=src[src.index(f'def {name}'):]; seg=seg[:seg.index('noncomputable def',10)]
  pat=r'\|\s*(\d+),\s*(\d+)\s*=>\s*\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)' if two else r'\|\s*(\d+)\s*=>\s*\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)'
  out={}
  for m in re.finditer(pat, seg):
    if two: out[(int(m.group(1)),int(m.group(2)))]=F(int(m.group(3)),int(m.group(4)))
    else: out[int(m.group(1))]=F(int(m.group(2)),int(m.group(3)))
  return out
BQ={}
for o in (False,True):
  d=parse(('odd' if o else 'even')+'Diag',False); u=parse(('odd' if o else 'even')+'Upper',True)
  BQ[o]=lambda i,j,d=d,u=u: d[i] if i==j else (u.get((i,j),F(0)) if i<j else F(0))
shiftQ={True:F(-16811071618091732846084088270431737827926921338759786126097413044023574083070857,4*10**78),
        False:F(-402335143495720182899444246584910110815483700126924367402028335615165576796512809,10**80)}
deg=lambda o,i: 2*i+(1 if o else 0)
def bsum(l):
  r=(0,0)
  for b in l: r=add(b,r) if False else add(r,b)
  return r
def bsum_lean(l):  # bsum (b :: bs) = add b (bsum bs)
  r=(0,0)
  for b in reversed(l): r=add(b,r)
  return r
def stages(o):
  A=[[entryB(deg(o,j),deg(o,i)) for j in range(32)] for i in range(32)]
  At=[[entryB(deg(o,j),deg(o,32+i)) for j in range(32)] for i in range(32)]
  Bb=[[qBall(BQ[o](i,j)) for j in range(32)] for i in range(32)]
  wi=[qBall(1/(H[deg(o,32+i)]+shiftQ[o])) for i in range(32)]
  BA=[[bsum_lean([mulB(Bb[i][p],A[i][j]) for i in range(32)]) for j in range(32)] for p in range(32)]
  T1=[[bsum_lean([mulB(BA[p][j],Bb[j][q]) for j in range(32)]) for q in range(32)] for p in range(32)]
  G=[[bsum_lean([mulB(Bb[j][p],At[i][j]) for j in range(32)]) for p in range(32)] for i in range(32)]
  T2=[[bsum_lean([mulB(mulB(G[i][p],G[i][q]),wi[i]) for i in range(32)]) for q in range(32)] for p in range(32)]
  M=[[sub(T1[p][q],T2[p][q]) for q in range(32)] for p in range(32)]
  return dict(A=A,At=At,Bb=Bb,wi=wi,BA=BA,T1=T1,G=G,T2=T2,M=M)
def rows(M,eta):
  worst=None
  for p in range(32):
    lo=F(M[p][p][0]-M[p][p][1],S)
    off=sum(F(abs(M[p][q][0])+M[p][q][1]+abs(M[q][p][0])+M[q][p][1],S) for q in range(32) if q!=p)/2
    val=lo-off-(1-eta)
    worst=val if worst is None or val<worst else worst
  return worst
if __name__=='__main__':
  for o,eta in ((False,F(1,10)),(True,F(1,25))):
    st=stages(o); w=rows(st['M'],eta)
    print('odd' if o else 'even','worst row slack',float(w),'Mpp radius',st['M'][0][0][1]/S)
