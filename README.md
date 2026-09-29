# Weil positivity on a window of width log 5 — Lean formalization

These sources were built on Linux and verified with the Lean FRO comparator; both the NanoDa kernel and the standard Lean kernel accepted both theorems (run `rh0605/final-001`, see "Status" and `evidence/`). The verification was run by the author; it is not a review by the tool developers or any other organization, and the mathematics has not yet been reviewed by human experts. No claim of the Riemann Hypothesis is made.

## Paper and archive

- Paper: R. Mori, *Weil positivity on a window of width log 5: a formal proof in Lean 4*, preprint, 2026, Zenodo, [doi:10.5281/zenodo.23034001](https://doi.org/10.5281/zenodo.23034001) (all versions).
- This code, release v1.0.0: Zenodo, [doi:10.5281/zenodo.23031523](https://doi.org/10.5281/zenodo.23031523).

## Theorems

Let `L = log(5)/2`. The Challenge (`trusted/Challenge.lean`) states two theorems about the Weil quadratic form `W` of the nontrivial zeros of the Riemann zeta function, with the definitions of the Zeta23 library:

- `RHLog5Release.target_log5`: for every nonzero complex C² function `f` with `f x ≠ 0 → |x| ≤ L`, the zero sum is summable and `0 < Re W(f,f)`. Proved in `candidate/Solution.lean` by `RHFinalAll0524.target_log5_concrete`.
- `RHLog5Release.target_log5_uniform`: there is `c > 0` such that for every complex C² function `f` with the same support condition (including `f = 0`), the zero sum is summable and `c ∫ ‖f‖² ≤ Re W(f,f)`. Proved by `RHUniform0579.uniform_target_log5`. The constant is not evaluated numerically.

## Layout

- `trusted/`: the Challenge and the seven trusted Zeta23 statement modules.
- `candidate/`: proof modules and the Solution.
- `tools/generators/`: Python scripts that produced the literal numerical tables, with an index (see its README). Not part of the trusted base.
- `comparator_config.json`: configuration for the Lean FRO comparator (both theorems, standard three axioms, NanoDa enabled).
- `DEPENDENCIES.json`: pinned dependency commits and Lean toolchain.
- `evidence/`: raw records of the verification runs, `#print axioms` output, and `check_evidence.py` (see `evidence/README.md`); `CHANGES_FROM_VERIFIED_SNAPSHOT.json` compares every Lean file with the snapshot of the earlier runs.
- `LICENSE` (Apache-2.0), `NOTICE`, `licenses/` (preserved upstream licence and notice texts).
- `MANIFEST.json`, `verify.py`: exact file inventory and byte checks, not a proof checker.

## Reproduction procedure

The verification run built these sources with the same pinned dependencies using the author's own run scripts (records in `evidence/rh0605/`); the commands below follow the same steps but have not been run verbatim. Prerequisites: Python 3, Git, elan, internet access for dependency retrieval; Lean 4.34.0. Allow at least 32 GB RAM and 25 GB free disk. Compile one heavy module at a time.

```sh
python3 verify.py
python3 prepare_deps.py
(cd deps/leancert && lake exe cache get)
(cd trusted && lake build Challenge)
(cd candidate && lake build Solution)
```

Do not run `lake update`: exact revisions are in the dependency lock. No olean files are included. The Challenge intentionally contains placeholders; the Solution must prove the same statements with only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

- **This release** was built afresh on Linux and verified with the Lean FRO comparator in run `rh0605/final-001`: the trusted statement exported from a trusted-only environment was identical to the one exported from the candidate environment, only `propext`, `Quot.sound`, and `Classical.choice` were permitted, and both the NanoDa kernel and the standard Lean kernel accepted both theorems. All 161,113 recorded inputs were unchanged before and after the run, and every `.lean` file of this repository is byte-identical to the file used in the run. `#print axioms` for both theorems lists only `propext`, `Classical.choice`, and `Quot.sound` (`evidence/rh0605/print_axioms.txt`).
- Earlier fixed snapshots of the same proofs were verified in the same way: the strict positivity theorem in run `rh0576/final-001`, the uniform bound in run `rh0581/final-001`. The release differs from that snapshot only in comments and headers (development-status notes, internal references, and names of tools used during development removed), removed debug commands (`#print`, `#check`, `#eval`), two renamed namespaces, a portable package layout, and one combined Challenge/Solution for both theorems (`evidence/CHANGES_FROM_VERIFIED_SNAPSHOT.json`).
- Not yet done: review by human experts; a literature comparison to establish novelty.

## Reading the sources

- **Size.** The two theorems depend on 501 Lean files besides Lean, Mathlib, and LeanCert: 433 written for this project, 62 from Zeta23 (7 trusted statement files and 55 proof files, 5 of them patched), and 6 from the interval library; 81,219 lines, about 20.9 MB, of which about 17.2 MB are literal numerical tables checked in the kernel.

- **Numbers in names.** Numbers such as `0512` in module names (`T5Final0512`), namespaces, and headers are internal work numbers of the development; they indicate the order in which parts were built and distinguish successive versions of a component.
- **Comments.** Some comments describe a module in terms of the development at the time it was written (for example "milestone", "input", or "conditional form"). The status of the final results is given only by the Challenge, the Solution, and the verification.

## Use of generative AI

Large parts of this Lean development were written with generative AI systems (Anthropic Claude, OpenAI GPT, Google Gemini) under the direction of the author, who takes responsibility for the content. Correctness of the formal part rests on the Lean kernel check. The accompanying paper describes the use of AI in more detail.

## Licence

Apache License 2.0 (`LICENSE`, `NOTICE`). Files from Zeta23 (Anthropic formal-math) and girving/interval keep their original Apache-2.0 notices; modified files are marked.

Author: Ryota Mori.
