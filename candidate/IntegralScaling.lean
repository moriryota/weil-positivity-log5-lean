import MathlibAll0483
open MeasureTheory Set
namespace RHTuckScaling

theorem quotient_scale (f : ℝ → ℂ) (c : ℂ) {L : ℝ} (hL : 0 < L) (u t : ℝ) :
    (c*f u-c*f ((L*t)/L))/((|L*u-L*t|:ℝ):ℂ) =
      (L:ℂ)⁻¹ * c * ((f u-f t)/((|u-t|:ℝ):ℂ)) := by
  rw [mul_div_cancel_left₀ t hL.ne',← mul_sub L u t,abs_mul,abs_of_pos hL]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem integral_scale (f : ℝ → ℂ) (c : ℂ) {L : ℝ} (hL : 0 < L) (u : ℝ) :
    (∫ y in (-L)..L, (c*f u-c*f (y/L))/((|L*u-y|:ℝ):ℂ)) =
      c * (∫ t in (-1:ℝ)..1, (f u-f t)/((|u-t|:ℝ):ℂ)) := by
  have ht := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1:ℝ)) (b := 1)
    (fun y : ℝ => (c*f u-c*f (y/L))/((|L*u-y|:ℝ):ℂ)) L
  simp only [mul_neg_one,mul_one] at ht
  rw [← ht]
  simp_rw [quotient_scale f c hL u]
  rw [intervalIntegral.integral_const_mul]
  rw [Complex.real_smul]
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp
end RHTuckScaling
