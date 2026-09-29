# Compatibility changes to Zeta23

Diffs of the five Zeta23 proof files that were changed to build with Lean 4.34.0 and Mathlib `5ed2965256`, against
the upstream formal-math commit `3635e748` (91 diff lines in total). Four follow Mathlib lemma renames; one replaces
`import Mathlib` by an import of a generated module listing the Mathlib modules available in the build cache. The
seven Zeta23 files on which the statements depend are byte-identical to upstream. The files in this release also carry
a modification notice in their headers.
