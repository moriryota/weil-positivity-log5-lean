import TargetFormBinding
import Mathlib.Algebra.Polynomial.Eval.Defs
open MeasureTheory Set
namespace RHWeilColumnCandidate

/-- Zero extension of an interval polynomial; endpoint representatives do not affect Lp. -/
noncomputable def zeroPoly (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  (Icc (-L) L).indicator (fun y => p.eval y) x

/-- Explicit column function of a polynomial. Its representation of the quadratic form is proved in
`RHLowBlock0494.targetQ_zp` and `RHG2Final0489.g2`.
The prime sum is fixed to n<5; its Weil interpretation requires L=log(5)/2.
The exterior is set to zero. Endpoints may be assigned arbitrarily for Lp. -/
noncomputable def column (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  if |x| < L then
    ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * p.eval x +
    (1/2:ℝ) * (∫ y in Icc (-L) L,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) +
    (1/2:ℝ) * (RH_Rebaseline.T_tail (L-x) + RH_Rebaseline.T_tail (L+x)) * p.eval x +
    2 * (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) * Real.cosh (x/2) -
    2 * (∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) * Real.sinh (x/2) -
    ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (zeroPoly L p (x-Real.log n) + zeroPoly L p (x+Real.log n))
  else 0

-- Declaration inspection only: this file contains no representation or MemLp theorem.
end RHWeilColumnCandidate
