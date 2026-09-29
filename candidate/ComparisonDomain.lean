import SquareComparison
import PolynomialLpMap
open Polynomial MeasureTheory Set Filter
open scoped ENNReal
namespace RHComparisonIntegral

lemma energy_finite_of_density {L : ℝ} {f : ℝ → ℂ}
    (hf : AEMeasurable f (volume.restrict (Icc (-L) L)))
    (hi : Integrable (density f)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) :
    RHComparisonEnergy.energy L f < ⊤ := by
  rw [energy_product hf]
  apply ENNReal.mul_lt_top (by norm_num)
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    (density_aemeasurable hf).aestronglyMeasurable
    (Eventually.of_forall (density_nonneg f))).mpr hi)

theorem polynomial_energy_finite (L : ℝ) (p : Polynomial ℂ) :
    RHComparisonEnergy.energy L (fun x => p.eval (x:ℂ)) < ⊤ := by
  have hm : Continuous (fun x : ℝ => p.eval (x:ℂ)) := by fun_prop
  exact energy_finite_of_density hm.measurable.aemeasurable (polynomial_density_integrable L p)

theorem residual_energy_finite {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (p : Polynomial ℂ) :
    RHComparisonEnergy.energy L (fun x => f x-p.eval (x:ℂ)) < ⊤ := by
  have hm : Continuous (fun x : ℝ => p.eval (x:ℂ)) := by fun_prop
  exact energy_finite_of_density ((Lp.aestronglyMeasurable f).aemeasurable.sub hm.measurable.aemeasurable)
    (residual_density_integrable f hf p)

theorem actual_polynomial_domain {L : ℝ} (hL : 0 ≤ L) (p : Polynomial ℂ) :
    RHComparisonEnergy.InDomain L (RHPolynomialLpMap.toLp L hL p) := by
  have heval : (fun x => (RHPolynomialLpMap.toLp L hL p) x) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x : ℝ => p.eval (x:ℂ)) := RHPolynomialLpMap.coe_poly hL p
  unfold RHComparisonEnergy.InDomain RHComparisonEnergy.intervalEnergy
  rw [RHComparisonEnergy.energy_congr_ae heval]
  exact polynomial_energy_finite L p

theorem actual_residual_domain {L : ℝ} (hL : 0 ≤ L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (p : Polynomial ℂ) :
    RHComparisonEnergy.InDomain L (f-RHPolynomialLpMap.toLp L hL p) := by
  have heval : (fun x => (RHPolynomialLpMap.toLp L hL p) x) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x : ℝ => p.eval (x:ℂ)) := RHPolynomialLpMap.coe_poly hL p
  have he : (fun x => (f-RHPolynomialLpMap.toLp L hL p) x) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x => f x-p.eval (x:ℂ)) := by
    filter_upwards [Lp.coeFn_sub f (RHPolynomialLpMap.toLp L hL p),
      heval] with x hx hp
    simpa only [Pi.sub_apply,hp] using hx
  unfold RHComparisonEnergy.InDomain RHComparisonEnergy.intervalEnergy
  rw [RHComparisonEnergy.energy_congr_ae he]
  exact residual_energy_finite f hf p
end RHComparisonIntegral
