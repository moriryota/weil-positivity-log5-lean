"""Verify exact source package bytes; this does not verify Lean proofs."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
manifest=json.loads((D/'MANIFEST.json').read_text())
actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.relative_to(D).parts[0] not in ('.git','deps','__pycache__') and p.relative_to(D).as_posix()!='MANIFEST.json'}
if actual!=set(manifest):raise SystemExit('FILE_SET_MISMATCH')
for name,h in manifest.items():
 p=D/name
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise SystemExit('HASH_MISMATCH: '+name)
print('SOURCE_PACKAGE_MATCH; not Lean verification or permission to publish')
