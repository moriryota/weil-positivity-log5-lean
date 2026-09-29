# 0515: exact Python mirror of the Lean ball ops (Ball0504 smul/add/sub, Rec2D0515 tnext) and literal-table generator.
from fractions import Fraction as Fr
import math, sys
def smul(a,d,b): return ((b[0]*a)//d, (b[1]*abs(a)+d-1)//d+1)
def add(b,c): return (b[0]+c[0], b[1]+c[1])
def sub(b,c): return (b[0]-c[0], b[1]+c[1])
def gz(bs,l): return bs[l] if l < len(bs) else (0,0)
def tnext(a,b,d,l,cs,cm,qs):
  out=[]
  while len(cs)>=2 and len(qs)>=1:
    c0,c1=cs[0],cs[1]; q=qs[0]
    out.append(sub(smul(a,d,add(smul(l+1,2*l+1,c1),smul(l,2*l+1,cm))),smul(b,d,q)))
    l+=1; cm=c0; cs=cs[1:]; qs=qs[1:]
  return out
def ratBall(S,N,D): return ((N*S)//D,1)
def rows(base,J):
  t=[base, tnext(1,0,1,0,base,gz(base,0),base)]
  for j in range(J-2):
    r1,r0=t[-1],t[-2]; t.append(tnext(2*j+3,j+1,j+2,0,r1,gz(r1,0),r0))
  return t
def ball_of_bounds(S,lo,hi):  # lo<=x<=hi rationals -> (c,r) with (c-r)/S<=lo, hi<=(c+r)/S
  c=math.floor((lo+hi)/2*S); r=math.ceil(max(c-lo*S, hi*S-c))+1
  return (c,r)
def lean_rows(t):
  return '[' + ',\n  '.join('[' + ', '.join(f'({c}, {r})' for c,r in row) + ']' for row in t) + ']'
def mulB(S,a,b): return ((a[0]*b[0])//S, (((abs(a[0])+a[1])*b[1]+abs(b[0])*a[1])+S-1)//S+1)
import re
def lean_rat(path,name):
  t=open(path).read(); m=re.search(r'def '+name+r' : ℚ := (-?\d+) ?/ ?(\d+)',t)
  return Fr(int(m.group(1)),int(m.group(2)))
def lean_row_defs(t,prefix='row'):
  defs='\n\n'.join(f'def {prefix}{j} : List Ball :=\n  [' + ', '.join(f'({c}, {r})' for c,r in row) + ']' for j,row in enumerate(t))
  tab='def tab : List (List Ball) := [' + ', '.join(f'{prefix}{j}' for j in range(len(t))) + ']'
  return defs+'\n\n'+tab
