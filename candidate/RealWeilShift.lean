import WeilShiftBound
import RealSpatialEndpoint
import ComparisonTail
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Set
open RHPoleShift RHPrimeShift RHWeilShift RH_LiteratureBridge

namespace RHRealWeil

/-- Half-width L = log 5 / 2. -/
noncomputable def L : ℝ := Real.log 5 / 2

/-- Exact spatial Weil form as appearing in the all-zero explicit formula
(RHRealSpatialEndpoint.full_zero_log5). -/
noncomputable def spatial_weil (f : ℝ → ℝ) : ℝ :=
  h0 * (∫ x, (f x)^2) +
  (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2) +
  2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2 -
  2*∑ n ∈ Finset.range 5,
    ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n)

/-- Full-zero endpoint identity connects W(f, f).re directly to spatial_weil f. -/
theorem spatial_weil_eq_full_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      spatial_weil f := by
  have h := RHRealSpatialEndpoint.full_zero_log5 f hf hs
  unfold spatial_weil h0
  exact h.2

/-- Exact shift bound for the spatial Weil form (even block):
Right-hand side is the actual applied form `spatial_weil f`. -/
theorem spatial_weil_shift_even (f : ℝ → ℝ) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : 0 ≤ 2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_even * (∫ x, (f x)^2) ≤ spatial_weil f := by
  unfold spatial_weil c_even
  linarith

/-- Exact shift bound for the spatial Weil form (odd block):
Right-hand side is the actual applied form `spatial_weil f`. -/
theorem spatial_weil_shift_odd (f : ℝ → ℝ) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : - P_penalty * (∫ x, (f x)^2) ≤
      2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_odd * (∫ x, (f x)^2) ≤ spatial_weil f := by
  unfold spatial_weil c_odd
  linarith

/-- Exact shift bound for the spatial Weil form (general block, no parity assumption):
Right-hand side is the actual applied form `spatial_weil f`. -/
theorem spatial_weil_shift_general (f : ℝ → ℝ) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : - P_penalty * (∫ x, (f x)^2) ≤
      2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_odd * (∫ x, (f x)^2) ≤ spatial_weil f :=
  spatial_weil_shift_odd f energy_E hE hprime hpole

/-- Direct shift bound on the actual Zeta23 Weil explicit formula W(f, f).re:
Combining spatial_weil_eq_full_zero with spatial_weil_shift_even. -/
theorem full_zero_weil_shift_even (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : 0 ≤ 2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_even * (∫ x, (f x)^2) ≤
      (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re := by
  rw [spatial_weil_eq_full_zero f hf hs]
  exact spatial_weil_shift_even f energy_E hE hprime hpole

/-- Direct shift bound on the actual Zeta23 Weil explicit formula W(f, f).re:
Combining spatial_weil_eq_full_zero with spatial_weil_shift_odd. -/
theorem full_zero_weil_shift_odd (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : - P_penalty * (∫ x, (f x)^2) ≤
      2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_odd * (∫ x, (f x)^2) ≤
      (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re := by
  rw [spatial_weil_eq_full_zero f hf hs]
  exact spatial_weil_shift_odd f energy_E hE hprime hpole

/-- Direct shift bound on the actual Zeta23 Weil explicit formula W(f, f).re:
Combining spatial_weil_eq_full_zero with spatial_weil_shift_general. -/
theorem full_zero_weil_shift_general (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) (energy_E : ℝ)
    (hE : energy_E + T_tail * (∫ x, (f x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) ≤
      B_prime * (∫ x, (f x)^2))
    (hpole : - P_penalty * (∫ x, (f x)^2) ≤
      2*(∫ x, f x*Real.cosh (x/2))^2 - 2*(∫ x, f x*Real.sinh (x/2))^2) :
    energy_E + c_odd * (∫ x, (f x)^2) ≤
      (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re :=
  full_zero_weil_shift_odd f hf hs energy_E hE hprime hpole

/-- Direct connection to ComparisonTail.residual_shifted with the exact c_even and c_odd:
For any residual r satisfying the shifted Weil comparison, the harmonic tail bound holds. -/
theorem log5_tail_bound_even
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) (Q : ℝ)
    (hQ : (RHComparisonEnergy.intervalEnergy L (RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N)).toReal +
      c_even * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q) :
    ((harmonic N : ℝ) + c_even) * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q :=
  RHComparisonTail.residual_shifted RHLog5Bridge.halfWidth_pos f hf N c_even Q hQ

theorem log5_tail_bound_odd
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) (Q : ℝ)
    (hQ : (RHComparisonEnergy.intervalEnergy L (RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N)).toReal +
      c_odd * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q) :
    ((harmonic N : ℝ) + c_odd) * ‖RHComparisonTail.residual RHLog5Bridge.halfWidth_pos f N‖^2 ≤ Q :=
  RHComparisonTail.residual_shifted RHLog5Bridge.halfWidth_pos f hf N c_odd Q hQ

end RHRealWeil

