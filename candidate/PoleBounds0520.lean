import BasisBound0520
import Mathlib.Analysis.Complex.ExponentialBounds

namespace RHPoleBounds0520
open MeasureTheory Set RHLog5Bridge RHConditionalLog5 RHColDecomp0499

lemma width_lt_one : halfWidth < 1 := by
  have h := RHEntry00Bounds0495.b_l5.2
  have hq : RHEntry00Bounds0495.l5H < 2 := by decide +kernel
  have hr := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at hr
  unfold halfWidth
  linarith

lemma hyp_bound {t : ℝ} (ht : |t| ≤ 1) : |Real.cosh t| ≤ 3 ∧ |Real.sinh t| ≤ 3 := by
  have ht' := abs_le.mp ht
  have ha := (Real.exp_le_exp.mpr ht'.2).trans Real.exp_one_lt_three.le
  have hb := (Real.exp_le_exp.mpr (show -t ≤ 1 by linarith)).trans Real.exp_one_lt_three.le
  have hpa := Real.exp_pos t
  have hpb := Real.exp_pos (-t)
  constructor
  · rw [abs_of_pos (Real.cosh_pos t), Real.cosh_eq]; linarith
  · rw [Real.sinh_eq, abs_div, abs_two, div_le_iff₀ (by norm_num), abs_le]
    constructor <;> linarith

lemma weighted_bound (n : ℕ) (hn : n ≤ 63) (f : ℝ → ℝ)
    (hf : ∀ x, |x| ≤ halfWidth → |f x| ≤ 3) :
    |∫ x in Icc (-halfWidth) halfWidth, (basisPoly n).eval x * f x| ≤ 100 := by
  rw [RHEntry00_0495.setI, ← Real.norm_eq_abs]
  have hL := halfWidth_pos
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := (27:ℝ))
    (a := -halfWidth) (b := halfWidth) (f := fun x => (basisPoly n).eval x * f x) (by
      intro x hx
      rw [Set.uIoc_of_le (by linarith : -halfWidth ≤ halfWidth)] at hx
      have hx' : |x| ≤ halfWidth := abs_le.mpr ⟨hx.1.le,hx.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := RHBasisBound0520.basis_bound n hn hx'
      have h2 := hf x hx'
      exact (mul_le_mul h1 h2 (abs_nonneg (f x)) (by norm_num : (0:ℝ) ≤ 9)).trans (by norm_num))
  have he : |halfWidth - -halfWidth| = 2*halfWidth := by rw [abs_of_pos (by linarith)]; ring
  rw [he] at h
  have hw := width_lt_one
  linarith

theorem Cc_bound (n : ℕ) (hn : n ≤ 63) : |Cc n| ≤ 100 := by
  apply weighted_bound n hn
  intro x hx
  have h : |x/2| ≤ 1 := by rw [abs_div, abs_two]; linarith [width_lt_one]
  exact (hyp_bound h).1

theorem Ss_bound (n : ℕ) (hn : n ≤ 63) : |Ss n| ≤ 100 := by
  apply weighted_bound n hn
  intro x hx
  have h : |x/2| ≤ 1 := by rw [abs_div, abs_two]; linarith [width_lt_one]
  exact (hyp_bound h).2
end RHPoleBounds0520
