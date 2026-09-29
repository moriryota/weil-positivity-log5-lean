import WeilShiftBound
import ComparisonTail

open MeasureTheory Set
open RHPoleShift RHPrimeShift RHWeilShift

namespace RHWeilIntegration

/-- Actual spatial Weil quadratic form instantiated on real Lp elements. -/
noncomputable def weil_form_lp
    (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (D : ℝ) : ℝ :=
  weil_form (‖f‖^2) D (pole_quad f c s) (prime_form f)

/-- Even block shift bound for real Lp functions:
Given Archimedean energy lower bound D ≥ E + T_tail * ‖f‖²
and even parity (inner ℝ f s = 0),
the actual Weil form is bounded below by E + c_even * ‖f‖². -/
theorem lp_weil_shift_even
    (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (E D : ℝ)
    (hE : E + T_tail * ‖f‖^2 ≤ D)
    (heven : is_even f s) :
    E + c_even * ‖f‖^2 ≤ weil_form_lp f c s D := by
  unfold weil_form_lp
  apply weil_shift_bound_even (‖f‖^2) E D (pole_quad f c s) (prime_form f) hE
  · exact prime_form_le f
  · exact pole_even_lower f c s heven

/-- Odd block shift bound for real Lp functions:
Given Archimedean energy lower bound D ≥ E + T_tail * ‖f‖²,
odd parity (inner ℝ f c = 0), and ‖s‖² ≤ sinh L - L,
the actual Weil form is bounded below by E + c_odd * ‖f‖². -/
theorem lp_weil_shift_odd
    (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (E D : ℝ)
    (hE : E + T_tail * ‖f‖^2 ≤ D)
    (hodd : is_odd f c)
    (hs : ‖s‖^2 ≤ Real.sinh L - L) :
    E + c_odd * ‖f‖^2 ≤ weil_form_lp f c s D := by
  unfold weil_form_lp
  have hP : - P_penalty * ‖f‖^2 ≤ pole_quad f c s := by
    unfold P_penalty
    have h := pole_odd_bound f c s hodd (Real.sinh L - L) hs
    linarith
  apply weil_shift_bound_odd (‖f‖^2) E D (pole_quad f c s) (prime_form f) hE
  · exact prime_form_le f
  · exact hP

/-- General shift bound for real Lp functions (no parity assumption):
Given Archimedean energy lower bound D ≥ E + T_tail * ‖f‖²
and ‖s‖² ≤ sinh L - L,
the actual Weil form is always bounded below by E + c_odd * ‖f‖². -/
theorem lp_weil_shift_general
    (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (E D : ℝ)
    (hE : E + T_tail * ‖f‖^2 ≤ D)
    (hs : ‖s‖^2 ≤ Real.sinh L - L) :
    E + c_odd * ‖f‖^2 ≤ weil_form_lp f c s D := by
  unfold weil_form_lp
  have hP : - P_penalty * ‖f‖^2 ≤ pole_quad f c s := by
    unfold P_penalty
    have h := pole_general_bound f c s (Real.sinh L - L) hs
    linarith
  apply weil_shift_bound_general (‖f‖^2) E D (pole_quad f c s) (prime_form f) hE
  · exact prime_form_le f
  · exact hP

/-- Tail transfer for even block:
Connecting comparison-tail residual with the even shift bound. -/
theorem log5_tail_transfer_even
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) (Q : ℝ)
    (hQ : (RHComparisonEnergy.intervalEnergy L (RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N)).toReal +
      c_even * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q) :
    ((harmonic N : ℝ) + c_even) * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q :=
  RHComparisonTail.residual_shifted RHLog5Bridge.halfWidth_pos f hf N c_even Q hQ

/-- Tail transfer for odd block:
Connecting comparison-tail residual with the odd shift bound. -/
theorem log5_tail_transfer_odd
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) (Q : ℝ)
    (hQ : (RHComparisonEnergy.intervalEnergy L (RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N)).toReal +
      c_odd * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q) :
    ((harmonic N : ℝ) + c_odd) * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q :=
  RHComparisonTail.residual_shifted RHLog5Bridge.halfWidth_pos f hf N c_odd Q hQ

end RHWeilIntegration

