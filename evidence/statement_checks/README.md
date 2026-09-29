# Printed types of the declarations cited in the paper

`CheckTypes0601.lean` prints, with `#check`, the Lean type of each of the 231 distinct declarations cited in the
accompanying paper (`names.txt`); `types_all.out` is its output, produced from a local build of the verified snapshot
(the sources of runs `rh0576/final-001` and `rh0581/final-001`). `coverage.json` records that every cited name was
printed without error. The release differs from that snapshot only as described in
`../CHANGES_FROM_VERIFIED_SNAPSHOT.json`; none of the cited declarations is in a renamed namespace.

This is a record of the statements. The comparison of each numbered result of the paper with these types was done by
reading, not by a mechanical equivalence check.
