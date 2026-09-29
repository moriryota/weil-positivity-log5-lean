import LegendreBound0520
import RpExact0506

namespace RHBasisBound0520
open RHLog5Bridge RHConditionalLog5 RHRpExact0506

lemma log5_gt : (8/5:ℝ) < Real.log 5 := by
  have h := RHEntry00Bounds0495.b_l5.1
  have hq : (8/5:ℚ) < RHEntry00Bounds0495.l5L := by decide +kernel
  have hr := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at hr
  exact hr.trans_le h

lemma cc_le_nine (n : ℕ) (hn : n ≤ 63) : cc n ≤ 9 := by
  unfold cc
  have hL := halfWidth_pos
  have hn' : (n:ℝ) ≤ 63 := by exact_mod_cast hn
  have hl : (8/5:ℝ) < 2*halfWidth := by
    unfold halfWidth
    linarith [log5_gt]
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · apply (div_le_iff₀ (by positivity : 0 < 2*halfWidth)).mpr
    nlinarith

theorem basis_bound (n : ℕ) (hn : n ≤ 63) {x : ℝ} (hx : |x| ≤ halfWidth) :
    |(basisPoly n).eval x| ≤ 9 := by
  have hL := halfWidth_pos
  have hu : |x/halfWidth| ≤ 1 := by
    rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; simpa using hx
  rw [RHLink0505.basisPoly_eval, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hp := RHLegendreBound0520.abs_p_le_one n hu
  have hc := cc_le_nine n hn
  have hc0 : 0 ≤ cc n := Real.sqrt_nonneg _
  change cc n * |RHLeg0503.p n (x/halfWidth)| ≤ 9
  exact (mul_le_mul_of_nonneg_left hp hc0).trans (by simpa using hc)
end RHBasisBound0520
