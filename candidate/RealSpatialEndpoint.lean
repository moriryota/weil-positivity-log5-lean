import EnergyFubini
import PoleFactor
import PrimeEndpoint

namespace RHRealSpatialEndpoint
open Real MeasureTheory RH_LiteratureBridge RHAutocorrEnergy

/-- Correct full-zero endpoint identity, for real C¹ tests, without positivity hypotheses. -/
theorem full_zero_log5 (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) (ρ : ℂ)) ∧
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi) * (∫ x, (f x)^2) +
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2) +
      2*(∫ x, f x*Real.cosh (x/2))^2-2*(∫ x, f x*Real.sinh (x/2))^2 -
      2*∑ n ∈ Finset.range 5,
        ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) := by
  refine ⟨(RHLog5Bridge.whole_zero_endpoint f hf hs).1, ?_⟩
  rw [whole_zero_eq_spatial RHLog5Bridge.halfWidth_pos hf hs,
    RHPoleFactor.pole_autocorr_cosh_sinh RHLog5Bridge.halfWidth_pos hf hs,
    RHPrimeEndpoint.prime_sum_endpoint f hf hs]
  unfold spatialEnergy
  ring
end RHRealSpatialEndpoint
