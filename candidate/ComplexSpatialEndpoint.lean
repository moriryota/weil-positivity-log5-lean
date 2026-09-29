import ComplexSplit
import ComplexEnergy

namespace RHComplexSpatialEndpoint
open Real MeasureTheory Set Zeta23 RH_LiteratureBridge RHComplexFrequency RHComplexSpatial
open scoped ComplexConjugate

/-- Full-zero summability and the complex spatial identity, on the exact log 5 support.
C² is explicit: the maximal upstream frequency-form theorem is reused. -/
theorem full_zero_log5 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    (zetaZeroConfig.W f f).re =
      ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi)*(∫ x, ‖f x‖^2) +
      complexSpatialEnergy f +
      2*‖∫ x, f x*(Real.cosh (x/2):ℂ)‖^2-2*‖∫ x, f x*(Real.sinh (x/2):ℂ)‖^2 -
      2*∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
        (∫ t, f t*conj (f (t-Real.log n))).re := by
  have hL := RHLog5Bridge.halfWidth_pos
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hc := compact_of_support hs
  have hrd : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf1
  have hid : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf1
  have hr := RHRealSpatialEndpoint.full_zero_log5 (fun x => (f x).re) hrd (re_support hs)
  have hi := RHRealSpatialEndpoint.full_zero_log5 (fun x => (f x).im) hid (im_support hs)
  refine ⟨(frequency_package hL hf hs).1, ?_⟩
  have hw := congrArg Complex.re (W_re_im hL hf hs)
  simp only [Complex.add_re] at hw
  have hsum : (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
      (∫ t, f t*conj (f (t-Real.log n))).re) =
      (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
        real_autocorr (fun x => (f x).re) (Real.log n)) +
      (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
        real_autocorr (fun x => (f x).im) (Real.log n)) := by
    simp_rw [autocorr_re_parts hf.continuous hc,mul_add]
    exact Finset.sum_add_distrib
  rw [hw,hr.2,hi.2,integral_norm_sq_parts hf.continuous hc,
    complex_spatial_parts hL hf1 hs,
    norm_integral_weight_parts hf.continuous hc (fun x => Real.cosh (x/2)) (by fun_prop),
    norm_integral_weight_parts hf.continuous hc (fun x => Real.sinh (x/2)) (by fun_prop),hsum]
  unfold RHAutocorrEnergy.spatialEnergy
  ring
end RHComplexSpatialEndpoint
