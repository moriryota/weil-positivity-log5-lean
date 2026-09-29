# 0521: Python mirror of LamDef0521.lamBase (exact), and Lean test/data generation
import sys
from ballops import *
from gen_tab import mulB as _m, lean_row_defs
def lamIter(S,kB,R):
  u=vunit(S,0); pw=(S,0); acc=[]
  for r in range(R):
    u=vX(u); pw=_m(S,pw,kB); c=smul(1 if r%2==0 else -1, r+1, pw); acc=vadd(acc,vscaleB(S,c,u))
  return u,pw,acc
def lamErr(S,kB,R):
  K=max(kB[0]+kB[1],0); D=S**R*(S-K); return (2*K**(R+1)*S+D-1)//D+1
def lamBase(S,kB,R,NL):
  acc=lamIter(S,kB,R)[2][:NL]; e=lamErr(S,kB,R)
  return [(smul(2,2*l+1,b)[0], smul(2,2*l+1,b)[1]+e) for l,b in enumerate(acc)]
