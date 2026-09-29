import DisplacementEnergy
import WindowSlices
import KernelMoment
import EnergyFubini

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain
open RHIntervalDifference
set_option maxHeartbeats 1000000

lemma full_moment_integrable {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun s => min |s| b * RH_GammaFinalFormula.K_kernel |s|) := by
  apply RHAutocorrEnergy.integrable_of_even_Ioi (by intro s; simp only [abs_neg])
  apply (truncated_kernel_integrable hb).congr_fun _ measurableSet_Ioi
  intro s hs
  simp only [abs_of_pos (show 0 < s from hs)]

lemma full_moment_nonneg {b : ℝ} (hb : 0 ≤ b) (s : ℝ) :
    0 ≤ min |s| b * RH_GammaFinalFormula.K_kernel |s| :=
  mul_nonneg (le_min (abs_nonneg s) hb) (RHAutocorrEnergy.kernel_abs_nonneg s)

/-- The exact ENNReal energy, not a separate model of the interval energy. -/
theorem cwindow_energy {b : ℝ} (hb : 0 ≤ b) :
    energy (cwindow b) = ENNReal.ofReal
      (∫ s in Ioi (0:ℝ), min s b * RH_GammaFinalFormula.K_kernel s) := by
  rw [energy_displacement (measurable_cwindow b)]
  simp_rw [cwindow_difference]
  have hn (s : ℝ) : kernel s ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ (hn _), shift_lintegral hb]
  have he (s : ℝ) : kernel s*ENNReal.ofReal (2*min |s| b) =
      ENNReal.ofReal (2*(min |s| b*RH_GammaFinalFormula.K_kernel |s|)) := by
    rw [kernel_eq_old, ← ENNReal.ofReal_mul (RHAutocorrEnergy.kernel_abs_nonneg s)]
    congr 1
    ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal ((full_moment_integrable hb).const_mul 2)
    (Filter.Eventually.of_forall (fun s => mul_nonneg (by norm_num) (full_moment_nonneg hb s)))]
  rw [integral_const_mul, integral_comp_abs (f := fun s => min s b * RH_GammaFinalFormula.K_kernel s)]
  simp only [← mul_assoc, show (2:ℝ)*2=4 by norm_num,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  rw [ENNReal.inv_mul_cancel (by norm_num : (4:ℝ≥0∞) ≠ 0) (by norm_num : (4:ℝ≥0∞) ≠ ⊤), one_mul]

lemma cwindow_energy_finite {b : ℝ} (hb : 0 ≤ b) : energy (cwindow b) < ⊤ := by
  rw [cwindow_energy hb]
  exact ENNReal.ofReal_lt_top
end RHFormDomain
