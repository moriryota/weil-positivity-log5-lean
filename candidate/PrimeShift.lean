import JointPrimeLoss
import PrimeConstants

open MeasureTheory Set
open RHPrimeConstants RHActualPrime3 RHActualCorrelation
open RHJointPrimeBound

namespace RHPrimeShift

/-- Prime quadratic upper bound constant B_234 = λ + μ₃ - γ. -/
noncomputable def B_prime : ℝ :=
  lam (Real.log 2) + mu3 - log5_gamma

/-- The combined prime-shift form on real Lp. -/
noncomputable def prime_form
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) : ℝ :=
  2 * alpha (Real.log 2) * autocorr (Real.log 5/2) f (Real.log 2) +
  2 * beta (Real.log 2) * autocorr (Real.log 5/2) f (Real.log 4) +
  2 * mu3 * autocorr (Real.log 5/2) f (Real.log 3)

/-- Upper bound for the prime quadratic form from milestone 0329. -/
theorem prime_form_le
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    prime_form f ≤ B_prime * ‖f‖^2 := by
  unfold prime_form B_prime
  exact log5_prime_joint_bound f

/-- Negated prime form satisfies the corresponding lower bound. -/
theorem neg_prime_form_ge
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    - B_prime * ‖f‖^2 ≤ - prime_form f := by
  have h := prime_form_le f
  linarith

end RHPrimeShift

