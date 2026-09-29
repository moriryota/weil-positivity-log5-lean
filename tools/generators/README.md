# Table generators

These Python scripts produced the literal numerical tables of the Lean development during its construction.
They are included for transparency and reproducibility of the tables. They are **not** part of the trusted base:
every table is checked inside Lean (by `decide +kernel` or by proofs), so an error in a script can only make the
Lean build fail, not make a false statement pass.

- `INDEX.json` maps each module that contains large literal tables to its generator:
  "output file name pattern in the script" (the script writes that file), "named in the module header",
  or "not identified" (small hand-written tables, or tables obtained during development by evaluating Lean
  definitions or by one-off commands that were not kept).
- Scripts are grouped by the internal work number of the task that created them (the number in the module names).
- Absolute paths of the development machine were replaced by `<DEV>/`; some scripts read intermediate data
  produced by earlier steps or by Lean evaluation. The scripts are therefore not guaranteed to run unchanged.
- Some files are helper modules imported by the generators and are therefore not listed in `INDEX.json`:
  `0512/t5mirror.py`, `0515/gen_tab.py`, `0521/ballops.py`, `0521/gen_lam.py`, `0521/gen_tab.py`,
  `0522/ballops.py`, `0522/gen_tab.py`.
- Python 3 with `mpmath` was used.
