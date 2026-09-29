import Truncation0520
import BasisBound0520
import RpErr0506

open MeasureTheory Set
namespace RHKernelError0520
open RHLog5Bridge RHConditionalLog5 RHColDecomp0499 RHTruncation0520

lemma polynomial_inner_ii (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y => RHPolyL0500.ev q63 (|x-y|/2) *
      ((basisPoly n).eval x - (basisPoly n).eval y)) volume (-halfWidth) halfWidth := by
  apply Continuous.intervalIntegrable
  exact ((RHRpErr0506.ev_cont _).comp
    ((continuous_const.sub continuous_id).abs.div_const 2)).mul
    (continuous_const.sub (basisPoly n).continuous)

lemma integral_error (n : ℕ) (hn : n ≤ 63) {x : ℝ} (hx : |x| ≤ halfWidth) :
    |(∫ y in (-halfWidth)..halfWidth, Rk |x-y| * ((basisPoly n).eval x - (basisPoly n).eval y)) -
      (∫ y in (-halfWidth)..halfWidth, RHPolyL0500.ev q63 (|x-y|/2) *
        ((basisPoly n).eval x - (basisPoly n).eval y))| ≤ 36*halfWidth/(10^18:ℝ) := by
  have hL := halfWidth_pos
  have hxI : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp hx
  rw [← intervalIntegral.integral_sub (RHRpErr0506.Rk_inner_ii n hxI) (polynomial_inner_ii n x)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (C := (18/10^18:ℝ)) (a := -halfWidth) (b := halfWidth)
    (f := fun y => Rk |x-y| * ((basisPoly n).eval x - (basisPoly n).eval y) -
      RHPolyL0500.ev q63 (|x-y|/2) * ((basisPoly n).eval x - (basisPoly n).eval y)) (by
      filter_upwards [Measure.ae_ne volume x] with y hne hy
      rw [Set.uIoc_of_le (by linarith : -halfWidth ≤ halfWidth)] at hy
      have hy' : |y| ≤ halfWidth := abs_le.mpr ⟨hy.1.le,hy.2⟩
      have hs : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
      have hs5 : |x-y| ≤ Real.log 5 := by
        rw [← RHRpErr0506.twoL, abs_le]
        constructor <;> linarith [hxI.1,hxI.2,hy.1,hy.2]
      have hr := rk63_approx hs hs5
      have hb : |(basisPoly n).eval x - (basisPoly n).eval y| ≤ 18 := by
        have hb' := (abs_sub ((basisPoly n).eval x) ((basisPoly n).eval y)).trans
          (add_le_add (RHBasisBound0520.basis_bound n hn hx)
            (RHBasisBound0520.basis_bound n hn hy'))
        norm_num at hb' ⊢
        exact hb' 
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      have hh := mul_le_mul hr hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/10^18)
      convert hh using 1 <;> ring)
  rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < halfWidth - -halfWidth)] at h
  convert h using 1 <;> ring

theorem kernel_error (n : ℕ) (hn : n ≤ 63) {x : ℝ} (hx : |x| ≤ halfWidth) :
    |(1/2:ℝ)*(∫ y in Icc (-halfWidth) halfWidth, Rk |x-y| * ((basisPoly n).eval x - (basisPoly n).eval y)) -
      (1/2:ℝ)*(∫ y in Icc (-halfWidth) halfWidth, RHPolyL0500.ev q63 (|x-y|/2) *
        ((basisPoly n).eval x - (basisPoly n).eval y))| ≤ 18*halfWidth/(10^18:ℝ) := by
  simp only [RHEntry00_0495.setI]
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  have h := integral_error n hn hx
  linarith

end RHKernelError0520
