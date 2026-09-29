import ExternalWeight
import FormDomain
import NormMass
open MeasureTheory Set
open scoped ENNReal
namespace RHEnergyMass

lemma external_lintegral_lower {L x : ℝ} (hx : |x| < L) :
    (2 : ℝ≥0∞) * ENNReal.ofReal (RH_Rebaseline.T_tail L) ≤
      ∫⁻ y in (Icc (-L) L)ᶜ, RHFormDomain.kernel (x-y) := by
  obtain ⟨hi, hb⟩ := RHExternalPotential.actual_external_weight hx
  have hn : ∀ y : ℝ, 0 ≤ RH_Rebaseline.K_kernel |x-y| := by
    intro y
    exact div_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr (abs_nonneg _))
  have heq := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)
  have hh : 2 * RH_Rebaseline.T_tail L ≤
      ∫ y in (Icc (-L) L)ᶜ, RH_Rebaseline.K_kernel |x-y| := by linarith
  calc
    (2 : ℝ≥0∞) * ENNReal.ofReal (RH_Rebaseline.T_tail L) =
        ENNReal.ofReal (2 * RH_Rebaseline.T_tail L) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ ENNReal.ofReal (∫ y in (Icc (-L) L)ᶜ, RH_Rebaseline.K_kernel |x-y|) :=
      ENNReal.ofReal_le_ofReal hh
    _ = ∫⁻ y in (Icc (-L) L)ᶜ, RHFormDomain.kernel (x-y) := heq

theorem cross_mass_lower {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    (2 : ℝ≥0∞) * ENNReal.ofReal (RH_Rebaseline.T_tail L) * ENNReal.ofReal (‖f‖^2) ≤
      ∫⁻ x in Icc (-L) L, ∫⁻ y in (Icc (-L) L)ᶜ,
        RHFormDomain.kernel (x-y) * ENNReal.ofReal (‖f x‖^2) := by
  have hc : (2 : ℝ≥0∞) * ENNReal.ofReal (RH_Rebaseline.T_tail L) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  rw [← norm_mass L f,
    ← lintegral_const_mul' _ (fun x : ℝ => ENNReal.ofReal (‖f x‖^2)) hc]
  apply lintegral_mono_ae
  have hmem : ∀ᵐ x ∂volume.restrict (Icc (-L) L), x ∈ Ioo (-L) L := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with x hx
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' (external_lintegral_lower (abs_lt.mpr hx)) le_rfl

end RHEnergyMass
