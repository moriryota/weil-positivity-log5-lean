# Compile <trial>/MathlibAll0483.lean (see gen_umbrella.py). No shared cache is written.
from pathlib import Path
import subprocess,os,json,hashlib,datetime,time
D=Path(__file__).resolve().parent;REPO=D.parents[3]
E=json.loads((REPO/'docs/ai_coordination/research/20260923_0481/environment.json').read_text())
W=Path('<DEV>/tool_trials/rh_main_0481');src=W/'MathlibAll0483.lean';out=src.with_suffix('.olean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
L=D/'builds'/'MathlibAll0483';L.mkdir(parents=True,exist_ok=True);k=len(list(L.glob('*.json')))+1;p=L/str(k)
p.with_suffix('.lean').write_bytes(src.read_bytes())
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(W),*E['paths']])
cmd=['/usr/bin/time','-l',E['lean'],'-j1','-o',str(out),str(src)];b=datetime.datetime.now().astimezone().isoformat();t=time.monotonic();before=sha(src)
r=subprocess.run(cmd,cwd=W,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=900)
p.with_suffix('.log').write_text(r.stdout)
info=dict(command=cmd,cwd=str(W),LEAN_PATH=env['LEAN_PATH'],started=b,ended=datetime.datetime.now().astimezone().isoformat(),seconds=round(time.monotonic()-t,2),exit_code=r.returncode,sha_before=before,sha_after=sha(src),olean_sha=sha(out) if out.exists() and r.returncode==0 else None)
p.with_suffix('.json').write_text(json.dumps(info,indent=1)+'\n');print(info['exit_code'],info['seconds'],r.stdout[-800:])
