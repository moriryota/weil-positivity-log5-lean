# Verification evidence

Raw records of the verification runs, kept unchanged as they were produced. The runs were made by the author with the
Lean FRO comparator (commit `d03acab1`), lean4export (`076e8e57`), and NanoDa (`68d5ca9d`) on Lean 4.34.0, on a
Linux machine, as an unprivileged user in a Landlock sandbox with the inputs protected against writing. They are not
reviews or endorsements by the tool developers or by any other organization.

Check the records with `python3 evidence/check_evidence.py` (reads the archives; does not rerun anything).

| Run | Sources | Theorems | Comparator time | Recorded inputs | Result |
|---|---|---|---|---|---|
| `rh0605/final-001` | **this release** | `RHLog5Release.target_log5`, `RHLog5Release.target_log5_uniform` | 6 h 8 min | 161,113 | NanoDa and Lean kernels accept |
| `rh0576/final-001` | earlier fixed snapshot | `RHLog5Audit0527.target_log5` | 6 h 57 min | 150,981 | NanoDa and Lean kernels accept |
| `rh0581/final-001` | earlier fixed snapshot + `Uniform0579.lean` | `RHLog5Uniform0580.target_log5_uniform` | 6 h 8 min | 154,024 | NanoDa and Lean kernels accept |

In each run the inputs (sources, build outputs, dependencies, and tool binaries, with their SHA-256 hashes) were
recorded before and after the run and were identical, and the trusted statement exported from a trusted-only
environment was identical to the one exported from the candidate environment. The tool binaries had the same hashes in
all three runs.

For `rh0605/final-001`, every `.lean` file under `candidate/` and `trusted/` of this repository is byte-identical to
the corresponding recorded input, and the run used no other `.lean` file under its project directories
(`check_evidence.py` checks this).

## Files

- `rh0605/final-evidence.tar.gz`: configuration, the two statement exports (their hashes only; the 404 MB exports
  themselves are not included), comparator output, the input maps before and after, and the run script.
- `rh0605/prepare-evidence.tar.gz`: the fresh build of this release on the same machine (per-module build logs,
  source hashes before and after, dependency resolution, isolation checks).
- `rh0605/print_axioms.txt`, `rh0605/Probe.lean`: `#print axioms` for both theorems after the build.
- `rh*/verification.json`: a summary of each archive, written when the archive was collected.
- `CHANGES_FROM_VERIFIED_SNAPSHOT.json`: the Lean files of this release compared with the snapshot of the earlier runs.
- `statement_checks/`: the printed Lean types of the 231 declarations cited in the paper.
- `zeta23_patches/`: the compatibility changes to five Zeta23 proof files, as diffs against upstream.

The records of the earlier runs show the module and namespace names of that snapshot, including names that were changed
for this release, and paths of the verification machine. Some scripts carry comments from the development, which used
generative AI (see the main README).
