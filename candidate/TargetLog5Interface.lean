import WholeZeroBridge
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-
# TargetLog5Interface.lean

Interface and statement definitions for milestone TARGET_LOG5:
"Strict positivity of the full Weil explicit quadratic form for all non-zero
complex C_c^2 test functions supported in [-log 5 / 2, log 5 / 2]."

Reuses RHLog5Bridge.halfWidth and halfWidth_pos directly.
-/

namespace RHTargetLog5Interface

open Real
open RHLog5Bridge

/-- Predicate for a valid C_c^2 test function on the log 5 window:
f is C^2, supported in [-log 5 / 2, log 5 / 2], and f ≠ 0. -/
def IsLog5TestFunction (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ (∀ x, f x ≠ 0 → |x| ≤ halfWidth) ∧ f ≠ 0

/-- If f is non-zero, then its real part is non-zero or its imaginary part is non-zero. -/
lemma re_ne_zero_or_im_ne_zero {f : ℝ → ℂ} (hn : f ≠ 0) :
    (fun x => (f x).re) ≠ 0 ∨ (fun x => (f x).im) ≠ 0 := by
  contrapose! hn
  ext x
  apply Complex.ext
  · change (fun y => (f y).re) x = 0
    rw [hn.1]
    rfl
  · change (fun y => (f y).im) x = 0
    rw [hn.2]
    rfl

/-- Support inclusion: if support of f is within L ≤ halfWidth, it is within halfWidth. -/
lemma support_le_trans {f : ℝ → ℂ} {L : ℝ}
    (hL : L ≤ halfWidth) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    ∀ x, f x ≠ 0 → |x| ≤ halfWidth :=
  fun x hx => (hs x hx).trans hL

end RHTargetLog5Interface

