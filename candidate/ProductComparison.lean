import ComparisonEnergy
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Set Filter
open scoped ENNReal
namespace RHComparisonIntegral

noncomputable def density (f : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  |z.1-z.2|⁻¹ * ‖f z.1-f z.2‖^2

lemma density_nonneg (f : ℝ → ℂ) (z : ℝ × ℝ) : 0 ≤ density f z :=
  mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (sq_nonneg _)

lemma density_aemeasurable {L : ℝ} {f : ℝ → ℂ}
    (hf : AEMeasurable f (volume.restrict (Icc (-L) L))) :
    AEMeasurable (density f)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  have hk : Measurable (fun z : ℝ × ℝ => |z.1-z.2|⁻¹) :=
    (by
      have hc : Continuous (fun z : ℝ × ℝ => |z.1-z.2|) := by fun_prop
      exact hc.measurable.inv)
  exact hk.aemeasurable.mul ((hf.comp_fst.sub hf.comp_snd).norm.pow_const 2)

lemma energy_product {L : ℝ} {f : ℝ → ℂ}
    (hf : AEMeasurable f (volume.restrict (Icc (-L) L))) :
    RHComparisonEnergy.energy L f = (4:ℝ≥0∞)⁻¹ *
      ∫⁻ z, ENNReal.ofReal (density f z)
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  rw [lintegral_prod _ (density_aemeasurable hf).ennreal_ofReal]
  unfold RHComparisonEnergy.energy RHComparisonEnergy.kernel density
  congr 1
  apply lintegral_congr_ae
  filter_upwards [] with x
  apply lintegral_congr_ae
  filter_upwards [] with y
  exact (ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))).symm

theorem integrable_density {L : ℝ} {f : ℝ → ℂ}
    (hf : AEMeasurable f (volume.restrict (Icc (-L) L)))
    (hE : RHComparisonEnergy.energy L f < ⊤) :
    Integrable (density f)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  have he := energy_product hf
  have hfin : (∫⁻ z, ENNReal.ofReal (density f z)
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) ≠ ⊤ := by
    rw [he] at hE
    exact (ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt hE) (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ 0)).ne
  have h := integrable_toReal_of_lintegral_ne_top
    (density_aemeasurable hf).ennreal_ofReal hfin
  simpa only [ENNReal.toReal_ofReal (density_nonneg f _)] using h

theorem energy_integral {L : ℝ} {f : ℝ → ℂ}
    (hf : AEMeasurable f (volume.restrict (Icc (-L) L)))
    (hE : RHComparisonEnergy.energy L f < ⊤) :
    (RHComparisonEnergy.energy L f).toReal = (1/4:ℝ) *
      ∫ z, density f z
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  rw [energy_product hf, ENNReal.toReal_mul]
  have he := integral_toReal (density_aemeasurable hf).ennreal_ofReal
    (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top :
      ∀ z : ℝ × ℝ, ENNReal.ofReal (density f z) < ⊤))
  rw [← he]
  simp only [ENNReal.toReal_ofReal (density_nonneg f _)]
  norm_num

 theorem actual_Lp_integral {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (hf : RHComparisonEnergy.InDomain L f) :
    Integrable (density f)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) ∧
    (RHComparisonEnergy.intervalEnergy L f).toReal = (1/4:ℝ) *
      ∫ z, density f z
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) :=
  ⟨integrable_density (Lp.aestronglyMeasurable f).aemeasurable hf,
   energy_integral (Lp.aestronglyMeasurable f).aemeasurable hf⟩
end RHComparisonIntegral
