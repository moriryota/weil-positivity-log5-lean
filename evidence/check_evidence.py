"""Check the recorded verification evidence of this release.

Run from the repository root:  python3 evidence/check_evidence.py
It reads the archives only; it does not rerun Lean or the comparator.
It checks, for run rh0605/final-001 (the run of this release):
  - the archive hash recorded in evidence/rh0605/verification.json,
  - comparator exit code 0 and the three acceptance messages (NanoDa kernel, Lean kernel, final verdict),
  - the configuration: both theorems, no definitions, only propext / Quot.sound / Classical.choice, NanoDa enabled,
  - identical exports of the trusted statement from the trusted and candidate environments,
  - identical input maps before and after the run,
  - every .lean file under candidate/ and trusted/ of this repository is byte-identical to the file
    recorded in the inputs of the run, and the run used no other .lean file under its project directories.
For the earlier runs rh0576 and rh0581 (fixed snapshots before this release) it checks the archive hashes
and the acceptance messages."""
from pathlib import Path, PurePosixPath
import hashlib, json, tarfile
ROOT = Path(__file__).resolve().parent.parent
E = ROOT / 'evidence'
MARKERS = ['nanoda kernel accepts the solution', 'Lean default kernel accepts the solution', 'Your solution is okay!']

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def members(t):
    ms = t.getmembers()
    assert all(m.isfile() and not PurePosixPath(m.name).is_absolute() and '..' not in PurePosixPath(m.name).parts for m in ms), 'unsafe archive member'
    return {m.name: m for m in ms}

def read(t, ms, suffix):
    [n] = [n for n in ms if n.endswith(suffix)]
    return t.extractfile(ms[n]).read()

report = {}
# run of this release
v = json.loads((E / 'rh0605/verification.json').read_text())
a = E / 'rh0605/final-evidence.tar.gz'
assert sha(a) == v['archive_sha256'], 'rh0605 archive hash'
with tarfile.open(a) as t:
    ms = members(t)
    j = lambda s: json.loads(read(t, ms, 'final-001/' + s))
    before, after = j('inputs.before.json'), j('inputs.after.json')
    cfg, res, exp = j('config.json'), j('comparator.result.json'), j('challenge-export-comparison.json')
    out = read(t, ms, 'final-001/comparator.stdout').decode()
assert before == after, 'inputs changed during the run'
assert res['exit_code'] == 0 and all(m in out for m in MARKERS), 'comparator did not accept'
assert cfg['theorem_names'] == ['RHLog5Release.target_log5', 'RHLog5Release.target_log5_uniform']
assert cfg['definition_names'] == [] and cfg['enable_nanoda'] is True
assert sorted(cfg['permitted_axioms']) == ['Classical.choice', 'Quot.sound', 'propext']
assert exp['identical'] and exp['trusted_sha256'] == exp['candidate_sha256']
pre = '/home/rhcheck/palomar0389/rh0605/'
local = {str(p.relative_to(ROOT)): sha(p) for d in ('candidate', 'trusted') for p in (ROOT / d).rglob('*.lean')}
recorded = {k[len(pre):]: h for k, h in before.items() if k.startswith(pre) and k.endswith('.lean')}
assert local == recorded, ('source mismatch', sorted(set(local) ^ set(recorded))[:5],
                           [k for k in local if k in recorded and local[k] != recorded[k]][:5])
report['rh0605/final-001'] = {'accepted': True, 'theorems': cfg['theorem_names'], 'recorded_inputs': len(before),
                              'lean_files_bound_to_this_repository': len(local),
                              'comparator_seconds': round(res['ended'] - res['started'])}
# earlier runs
for run in ('rh0576', 'rh0581'):
    v = json.loads((E / run / 'verification.json').read_text())
    a = E / run / 'final-evidence.tar.gz'
    assert sha(a) == v['archive_sha256'], run + ' archive hash'
    with tarfile.open(a) as t:
        ms = members(t)
        out = read(t, ms, 'final-001/comparator.stdout').decode()
        res = json.loads(read(t, ms, 'final-001/comparator.result.json'))
        cfg = json.loads(read(t, ms, 'final-001/config.json'))
    assert res['exit_code'] == 0 and all(m in out for m in MARKERS), run + ' not accepted'
    report[run + '/final-001'] = {'accepted': True, 'theorems': cfg['theorem_names'], 'note': 'fixed snapshot before this release'}
print(json.dumps(report, indent=1))
print('EVIDENCE_CONSISTENT; this checks recorded evidence, it does not rerun the verification')
