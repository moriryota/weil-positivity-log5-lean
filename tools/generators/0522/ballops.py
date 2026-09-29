# 0521: exact Python mirror of Lean ball list ops (BallVec0504, BallDot0509, CcBall0510, PrBall0511)
from gen_tab import smul, add, sub, mulB, gz, tnext, ratBall, ball_of_bounds
OPS={'mulB':0}
def mulBc(S,a,b): OPS['mulB']+=1; return mulB(S,a,b)
def zipP(f,A,B):
  n=max(len(A),len(B)); return [f(A[i] if i<len(A) else (0,0), B[i] if i<len(B) else (0,0)) for i in range(n)] if (A or B) else []
def vadd(A,B): return zipP(add,A,B)
def vsub(A,B): return zipP(sub,A,B)
def vsmul(a,d,B): return [smul(a,d,b) for b in B]
def vX(bs):
  Bv=[smul(l+1,2*l+1,b) for l,b in enumerate(bs)]; Cv=[smul(l,2*l+1,b) for l,b in enumerate(bs)]
  return vadd([(0,0)]+Bv, Cv[1:])
def vscaleB(S,a,bs): return [mulBc(S,a,b) for b in bs]
def vunit(S,n): return [(0,0)]*n+[(S,0)]
def afNext(S,aB,gB,l,b1,b0): return vsub(vsmul(2*l+3,l+2,vadd(vscaleB(S,aB,vX(b1)),vscaleB(S,gB,b1))), vsmul(l+1,l+2,b0))
def af1(S,aB,gB): return vadd(vscaleB(S,aB,vX(vunit(S,0))), vscaleB(S,gB,vunit(S,0)))
def afAll(S,aB,gB,N):
  out=[]; b0=vunit(S,0); b1=af1(S,aB,gB); l=0
  for c in range(N):
    out.append(b0); b0,b1=b1,afNext(S,aB,gB,l,b1,b0); l+=1
  return out
def dotB(S,A,B):
  acc=(0,0)
  for a,b in zip(A,B): acc=add(mulBc(S,a,b),acc)
  return acc
def dB(S,A,B): return dotB(S,A,[smul(2,2*j+1,b) for j,b in enumerate(B)])
def within(b,c,r,sh): return abs(b[0]-c*2**sh)+b[1] <= r*2**sh
def coarse(b,sh):
  c=(b[0]+2**(sh-1))>>sh; r=(abs(b[0]-c*2**sh)+b[1]+2**sh-1)>>sh
  assert within(b,c,r,sh); return (c,r)
def val(S,b): return b[0]/S, b[1]/S
