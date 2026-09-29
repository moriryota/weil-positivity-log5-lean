import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic
namespace RHKernelElementary
lemma sinh_two_ratio_le_exp : Real.sinh 2 / 2 ≤ Real.exp 1 := by
  have he := Real.exp_one_lt_three
  have hp := Real.exp_pos 1
  have hn := Real.exp_pos (-2)
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    convert Real.exp_add 1 1 using 1 <;> norm_num
  rw [Real.sinh_eq, h2]
  nlinarith

lemma kernel_of_ratio {s : ℝ} (hs : 0 < s)
    (hr : Real.sinh s / s ≤ (Real.sinh 2 / 2) ^ (s/2)) :
    s⁻¹ ≤ Real.exp (s/2) / Real.sinh s := by
  have hp : 0 < Real.sinh s := Real.sinh_pos_iff.mpr hs
  have hb : 0 ≤ Real.sinh 2 / 2 := by positivity
  have he := Real.rpow_le_rpow hb sinh_two_ratio_le_exp (show 0 ≤ s/2 by positivity)
  rw [Real.exp_one_rpow] at he
  have h := hr.trans he
  have hm : Real.sinh s ≤ Real.exp (s/2) * s := (div_le_iff₀ hs).mp h
  apply (le_div_iff₀ hp).mpr
  calc
    s⁻¹ * Real.sinh s ≤ s⁻¹ * (Real.exp (s/2)*s) := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs.le)
    _ = Real.exp (s/2) := by field_simp

lemma log5_half_le_one : Real.log 5 / 2 ≤ 1 := by
  have he := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by convert Real.exp_add 1 1 using 1 <;> norm_num
  have h5 : (5:ℝ) < Real.exp 2 := by rw [h2]; nlinarith
  have hl : Real.log 5 < 2 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr h5
  linarith
end RHKernelElementary
