import PoleShift
import PrimeShift
import OriginalLower
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Set
open RHPoleShift RHPrimeShift

namespace RHWeilShift

/-- Half-width L = log 5 / 2. -/
noncomputable def L : ℝ := Real.log 5 / 2

/-- Base constant h₀ = Re ψ(1/4) - log π. -/
noncomputable def h0 : ℝ :=
  (Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi

/-- Tail constant T_tail(L) from RH_Rebaseline. -/
noncomputable def T_tail : ℝ :=
  RH_Rebaseline.T_tail L

/-- Odd pole penalty P_penalty = 2 * (sinh L - L). -/
noncomputable def P_penalty : ℝ :=
  2 * (Real.sinh L - L)

/-- Even block shift correction constant c₊ = h₀ + T_tail - B_prime. -/
noncomputable def c_even : ℝ :=
  h0 + T_tail - B_prime

/-- Odd block shift correction constant c₋ = h₀ + T_tail - B_prime - P_penalty. -/
noncomputable def c_odd : ℝ :=
  h0 + T_tail - B_prime - P_penalty

/-- Abstract spatial Weil quadratic form from energy, pole, and prime components. -/
noncomputable def weil_form (norm_sq energy_D pole prime : ℝ) : ℝ :=
  h0 * norm_sq + energy_D + pole - prime

/-- Even block shift bound:
If the Archimedean energy satisfies D ≥ E + T_tail * ‖f‖²,
the prime form satisfies M ≤ B_prime * ‖f‖²,
and the pole form satisfies P ≥ 0 (even parity),
then the Weil form satisfies Q ≥ E + c_even * ‖f‖². -/
theorem weil_shift_bound_even (norm_sq energy_E energy_D pole prime : ℝ)
    (hE : energy_E + T_tail * norm_sq ≤ energy_D)
    (hprime : prime ≤ B_prime * norm_sq)
    (hpole : 0 ≤ pole) :
    energy_E + c_even * norm_sq ≤ weil_form norm_sq energy_D pole prime := by
  unfold weil_form c_even
  linarith

/-- Odd block shift bound:
If the Archimedean energy satisfies D ≥ E + T_tail * ‖f‖²,
the prime form satisfies M ≤ B_prime * ‖f‖²,
and the pole form satisfies P ≥ - P_penalty * ‖f‖² (odd parity),
then the Weil form satisfies Q ≥ E + c_odd * ‖f‖². -/
theorem weil_shift_bound_odd (norm_sq energy_E energy_D pole prime : ℝ)
    (hE : energy_E + T_tail * norm_sq ≤ energy_D)
    (hprime : prime ≤ B_prime * norm_sq)
    (hpole : - P_penalty * norm_sq ≤ pole) :
    energy_E + c_odd * norm_sq ≤ weil_form norm_sq energy_D pole prime := by
  unfold weil_form c_odd
  linarith

/-- General shift bound:
Without parity assumptions, the odd bound holds universally since P ≥ - P_penalty * ‖f‖². -/
theorem weil_shift_bound_general (norm_sq energy_E energy_D pole prime : ℝ)
    (hE : energy_E + T_tail * norm_sq ≤ energy_D)
    (hprime : prime ≤ B_prime * norm_sq)
    (hpole : - P_penalty * norm_sq ≤ pole) :
    energy_E + c_odd * norm_sq ≤ weil_form norm_sq energy_D pole prime :=
  weil_shift_bound_odd norm_sq energy_E energy_D pole prime hE hprime hpole

/-- Comparison to odd constant: c_odd ≤ c_even when P_penalty ≥ 0. -/
theorem c_odd_le_c_even (hP : 0 ≤ P_penalty) : c_odd ≤ c_even := by
  unfold c_odd c_even
  linarith

/-- Harmonic tail transfer: combining comparison tail with the shift bound. -/
theorem residual_harmonic_shift (harmonic_N c norm_sq energy_E Q : ℝ)
    (htail : harmonic_N * norm_sq ≤ energy_E)
    (hshift : energy_E + c * norm_sq ≤ Q) :
    (harmonic_N + c) * norm_sq ≤ Q := by
  linarith

end RHWeilShift

