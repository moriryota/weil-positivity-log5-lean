import SquareComparison
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHComparisonIntegral

theorem polynomial_variational_bound {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (p : Polynomial ℂ) :
    (1/2:ℝ) * (∫ z, (RHTuckMixed.mixedDifference f p z).re
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) -
    (1/4:ℝ) * (∫ z, density (fun x => p.eval (x:ℂ)) z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) ≤
      (RHComparisonEnergy.intervalEnergy L f).toReal := by
  let μ := (volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))
  have ha : Integrable (density f) μ := (actual_Lp_integral f hf).1
  have hb : Integrable (density (fun x => p.eval (x:ℂ))) μ := polynomial_density_integrable L p
  have hc : Integrable (fun z => (RHTuckMixed.mixedDifference f p z).re) μ :=
    Complex.reCLM.integrable_comp (RHExpected0285.actual_polynomial_mixed f p).1
  have hnon : 0 ≤ ∫ z, density (fun x => f x-p.eval (x:ℂ)) z ∂μ :=
    integral_nonneg (density_nonneg _)
  rw [density_sub_polynomial] at hnon
  rw [integral_sub (f := fun z => density f z+ density (fun x => p.eval (x:ℂ)) z)
    (g := fun z => 2*(RHTuckMixed.mixedDifference f p z).re) (ha.add hb) (hc.const_mul 2),
    integral_add (f := density f) (g := density (fun x => p.eval (x:ℂ))) ha hb,
    integral_const_mul] at hnon
  rw [(actual_Lp_integral f hf).2]
  change (1/2:ℝ)*(∫ z, (RHTuckMixed.mixedDifference f p z).re ∂μ) -
    (1/4:ℝ)*(∫ z, density (fun x => p.eval (x:ℂ)) z ∂μ) ≤
    (1/4:ℝ)*(∫ z, density f z ∂μ)
  linarith
end RHComparisonIntegral
