import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RHSchurPositivity

/-- Strict positivity from Schur margin when low-degree norm is positive. -/
theorem positive_of_low_pos {s η τ Q : ℝ}
    (hs : 0 < s) (hmargin : η + τ < 1)
    (hbound : (1 - η - τ) * s ≤ Q) : 0 < Q := by
  have hm : 0 < 1 - η - τ := by linarith
  exact lt_of_lt_of_le (mul_pos hm hs) hbound

/-- Strict positivity for pure tail vectors (low-degree norm is zero).
When the element is non-zero, its norm is positive, so the tail lower bound
d_tail * ‖f‖² ≤ Q yields Q > 0 whenever d_tail > 0. -/
theorem positive_of_pure_tail {norm_sq d_tail Q : ℝ}
    (hnorm : 0 < norm_sq) (hd : 0 < d_tail)
    (htail : d_tail * norm_sq ≤ Q) : 0 < Q := by
  have hpos : 0 < d_tail * norm_sq := mul_pos hd hnorm
  exact lt_of_lt_of_le hpos htail

/-- Combined dichotomy for strict positivity of the full quadratic form:
For any non-zero element with norm_sq > 0, whether low-degree norm s > 0
or s = 0 (pure tail), the quadratic form Q is strictly positive. -/
theorem full_strict_positivity {norm_sq s η τ d_tail Q : ℝ}
    (hnorm : 0 < norm_sq)
    (hs_nonneg : 0 ≤ s)
    (hmargin : η + τ < 1)
    (hd : 0 < d_tail)
    (h_low : 0 < s → (1 - η - τ) * s ≤ Q)
    (h_tail : s = 0 → d_tail * norm_sq ≤ Q) :
    0 < Q := by
  rcases eq_or_lt_of_le hs_nonneg with heq | hlt
  · -- Case s = 0: pure tail
    exact positive_of_pure_tail hnorm hd (h_tail heq.symm)
  · -- Case s > 0: low-degree active
    exact positive_of_low_pos hlt hmargin (h_low hlt)

end RHSchurPositivity

