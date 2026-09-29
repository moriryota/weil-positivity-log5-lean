import DomainLinear
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain
set_option maxHeartbeats 800000

lemma energy_displacement {f : ℝ → ℂ} (hf : Measurable f) :
    energy f = (4:ℝ≥0∞)⁻¹ * ∫⁻ s, ∫⁻ x,
      kernel s * ENNReal.ofReal (‖f x-f (x-s)‖^2) := by
  have hc (x : ℝ) :
      (∫⁻ y, kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) =
      ∫⁻ s, kernel s*ENNReal.ofReal (‖f x-f (x-s)‖^2) := by
    have h := lintegral_sub_left_eq_self (μ := volume) (fun s =>
      kernel s*ENNReal.ofReal (‖f x-f (x-s)‖^2)) x
    simpa only [sub_sub_self] using h
  unfold energy
  simp_rw [hc]
  congr 1
  apply lintegral_lintegral_swap
  have hk := measurable_kernel
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
    kernel p.2 * ENNReal.ofReal (‖f p.1-f (p.1-p.2)‖^2))).aemeasurable

lemma energy_translate (f : ℝ → ℂ) (c : ℝ) :
    energy (fun x => f (x+c)) = energy f := by
  have hc (x : ℝ) :
      (∫⁻ y, kernel (x-y)*ENNReal.ofReal (‖f (x+c)-f (y+c)‖^2)) =
      ∫⁻ y, kernel ((x+c)-y)*ENNReal.ofReal (‖f (x+c)-f y‖^2) := by
    have h := lintegral_add_right_eq_self (μ := volume) (fun y =>
      kernel ((x+c)-y)*ENNReal.ofReal (‖f (x+c)-f y‖^2)) c
    simpa only [add_sub_add_right_eq_sub] using h
  unfold energy
  simp_rw [hc]
  congr 1
  exact lintegral_add_right_eq_self (μ := volume) (fun x => ∫⁻ y,
    kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) c
end RHFormDomain
