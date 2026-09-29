import TestRestriction
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
open MeasureTheory Set Filter
open scoped ENNReal
namespace RHEnergyToReal
open RHFormDomain

lemma energy_toReal {f : ℝ → ℂ} (hf : Measurable f) (hE : energy f < ⊤) :
    (energy f).toReal = (1/4:ℝ) * ∫ x, ∫ y,
      RH_GammaFinalFormula.K_kernel |x-y| * ‖f x-f y‖^2 := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => kernel (p.1-p.2)*ENNReal.ofReal (‖f p.1-f p.2‖^2)
  have hF : Measurable F := by
    dsimp [F]
    exact (RHFormDomain.measurable_kernel.comp (measurable_fst.sub measurable_snd)).mul
      ((hf.comp measurable_fst |>.sub (hf.comp measurable_snd)).norm.pow_const 2 |>.ennreal_ofReal)
  have hfin : (∫⁻ x : ℝ, ∫⁻ y : ℝ, F (x,y)) ≠ ⊤ := by
    exact (ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt hE) (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ 0)).ne
  have hi (x : ℝ) : (∫⁻ y : ℝ, F (x,y)).toReal = ∫ y,
      RH_GammaFinalFormula.K_kernel |x-y| * ‖f x-f y‖^2 := by
    have he (y : ℝ) : (F (x,y)).toReal =
        RH_GammaFinalFormula.K_kernel |x-y| * ‖f x-f y‖^2 := by
      dsimp [F]
      rw [ENNReal.toReal_mul, kernel_eq_old,
        ENNReal.toReal_ofReal (RHAutocorrEnergy.kernel_abs_nonneg _),
        ENNReal.toReal_ofReal (sq_nonneg _)]
    have hx : Measurable (fun y : ℝ => F (x,y)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [← integral_toReal (μ := volume) hx.aemeasurable
      (Eventually.of_forall (fun y => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
    simp_rw [he]
  have ho := integral_toReal hF.lintegral_prod_right'.aemeasurable
    (ae_lt_top hF.lintegral_prod_right' hfin)
  unfold energy
  rw [ENNReal.toReal_mul]
  change ((4:ℝ≥0∞)⁻¹).toReal * (∫⁻ x : ℝ, ∫⁻ y : ℝ, F (x,y)).toReal = _
  rw [← ho]
  simp_rw [hi]
  norm_num
end RHEnergyToReal
