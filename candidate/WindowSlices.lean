import IntervalDifference
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter
namespace RHIntervalDifference

lemma shift_square_integrable (b s : ℝ) :
    Integrable (fun x => (window b x-window b (x-s))^2) := by
  apply ((interval_one_integrable 0 b).add (interval_one_integrable s (b+s))).mono'
  · have hw : Measurable (window b) := measurable_const.indicator measurableSet_Ioc
    fun_prop
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [window, Set.indicator, mem_Ioc, Pi.add_apply]
    split_ifs <;> norm_num at * <;> grind

lemma shift_lintegral {b : ℝ} (hb : 0 ≤ b) (s : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((window b x-window b (x-s))^2)) =
      ENNReal.ofReal (2*min |s| b) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (shift_square_integrable b s)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  rw [shift_integral hb]

noncomputable def cwindow (b : ℝ) (x : ℝ) : ℂ := (window b x : ℂ)

lemma measurable_cwindow (b : ℝ) : Measurable (cwindow b) := by
  have hw : Measurable (window b) := measurable_const.indicator measurableSet_Ioc
  exact Complex.measurable_ofReal.comp hw

lemma cwindow_difference (b x s : ℝ) :
    ‖cwindow b x-cwindow b (x-s)‖^2 = (window b x-window b (x-s))^2 := by
  simp only [cwindow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
end RHIntervalDifference
