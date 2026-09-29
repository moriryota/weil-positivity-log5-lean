"""Fetch pinned dependencies. Does not run lake update or build proofs."""
from pathlib import Path
import json,subprocess,os
D=Path(__file__).resolve().parent
pins=json.loads((D/'DEPENDENCIES.json').read_text())
def run(*args,cwd=None):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def clone(record,dst):
 if dst.is_symlink():raise SystemExit("DEPENDENCY_SYMLINK: "+str(dst))
 if not dst.exists():
  run('git','clone','--no-checkout',record['url'],str(dst))
  run('git','checkout','--detach',record['rev'],cwd=dst)
 if run('git','rev-parse','HEAD',cwd=dst)!=record['rev']:raise SystemExit('DEPENDENCY_REV_MISMATCH: '+str(dst))
 if run('git','status','--porcelain','--untracked-files=no',cwd=dst):raise SystemExit('DEPENDENCY_DIRTY: '+str(dst))
 if (dst/'.lake/package-overrides.json').exists() or (dst/'.lake/package-overrides.json').is_symlink():raise SystemExit('DEPENDENCY_OVERRIDE: '+str(dst))
 tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=dst).decode().split('\0'))
 for root,dirs,files in os.walk(dst):
  for n in dirs:
   if (Path(root)/n).is_symlink():raise SystemExit("DEPENDENCY_SYMLINK: "+str(Path(root)/n))
  if Path(root)==dst:dirs[:]=[n for n in dirs if n not in ('.git','.lake')]
  for n in files:
   rel=str((Path(root)/n).relative_to(dst))
   if rel not in tracked:raise SystemExit('DEPENDENCY_UNTRACKED: '+rel)
clone(pins['LeanCert'],D/'deps/leancert')
for p in pins['packages']:clone(p,D/'deps/leancert/.lake/packages'/p['name'])
print('Pinned dependency checkouts ready; build and audit still required')
