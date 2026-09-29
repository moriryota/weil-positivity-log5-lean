import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

open MeasureTheory Set
namespace RHIntervalDifference
noncomputable def window (b x : ℝ) : ℝ := (Ioc 0 b).indicator (fun _ => 1) x

lemma short_shift {b s : ℝ} (hs : 0 ≤ s) (hsb : s ≤ b) (x : ℝ) :
    (window b x-window b (x-s))^2 =
      (Ioc 0 s).indicator (fun _ : ℝ => (1:ℝ)) x +
      (Ioc b (b+s)).indicator (fun _ : ℝ => (1:ℝ)) x := by
  simp only [window, Set.indicator, mem_Ioc]
  split_ifs <;> norm_num at * <;> grind

lemma long_shift {b s : ℝ} (_hb : 0 ≤ b) (hbs : b ≤ s) (x : ℝ) :
    (window b x-window b (x-s))^2 =
      (Ioc 0 b).indicator (fun _ : ℝ => (1:ℝ)) x +
      (Ioc s (b+s)).indicator (fun _ : ℝ => (1:ℝ)) x := by
  simp only [window, Set.indicator, mem_Ioc]
  split_ifs <;> norm_num at * <;> grind

lemma interval_one_integrable (a b : ℝ) :
    Integrable ((Ioc a b).indicator (fun _ : ℝ => (1:ℝ))) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact integrableOn_const (by simp)

lemma positive_shift_integral {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (∫ x, (window b x-window b (x-s))^2) = 2*min s b := by
  by_cases h : s ≤ b
  · simp_rw [short_shift hs h]
    rw [integral_add (interval_one_integrable 0 s) (interval_one_integrable b (b+s))]
    simp only [integral_indicator_const (1:ℝ) measurableSet_Ioc, smul_eq_mul, mul_one]
    rw [Real.volume_real_Ioc_of_le hs, Real.volume_real_Ioc_of_le (by linarith : b ≤ b+s)]
    rw [min_eq_left h]
    ring
  · have hbs : b ≤ s := le_of_not_ge h
    simp_rw [long_shift hb hbs]
    rw [integral_add (interval_one_integrable 0 b) (interval_one_integrable s (b+s))]
    simp only [integral_indicator_const (1:ℝ) measurableSet_Ioc, smul_eq_mul, mul_one]
    rw [Real.volume_real_Ioc_of_le hb, Real.volume_real_Ioc_of_le (by linarith : s ≤ b+s)]
    rw [min_eq_right hbs]
    ring

lemma shift_integral_even (b s : ℝ) :
    (∫ x, (window b x-window b (x-s))^2) =
      (∫ x, (window b x-window b (x- -s))^2) := by
  rw [← integral_add_right_eq_self (fun x => (window b x-window b (x-s))^2) s]
  apply integral_congr_ae
  filter_upwards with x
  simp only [add_sub_cancel_right, sub_neg_eq_add]
  ring

lemma shift_integral {b : ℝ} (hb : 0 ≤ b) (s : ℝ) :
    (∫ x, (window b x-window b (x-s))^2) = 2*min |s| b := by
  by_cases hs : 0 ≤ s
  · simpa only [abs_of_nonneg hs] using positive_shift_integral hb hs
  · rw [shift_integral_even]
    simpa only [abs_of_nonpos (le_of_not_ge hs)] using
      positive_shift_integral hb (neg_nonneg.mpr (le_of_not_ge hs))
end RHIntervalDifference
