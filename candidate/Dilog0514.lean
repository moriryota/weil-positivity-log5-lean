import LogMoment0508
import Mathlib.NumberTheory.ZetaValues

/-! # 0514: `∫₀¹ log t log(1−t) = 2 − π²/6` and the moment `κ₀ = ∫_{−1}^1 log(1+x) log(1−x)`

Monotone convergence with `−log(1−t) = Σ t^{n+1}/(n+1)` (Mathlib `hasSum_pow_div_log_of_abs_lt_one`),
`∫₀¹ t^m log t = −1/(m+1)²`, telescoping `1/((n+1)(n+2)²) = 1/(n+1) − 1/(n+2) − 1/(n+2)²`
and Mathlib `hasSum_zeta_two`. Then `κ₀ = 2 log²2 − 4 log 2 + 4 − π²/3` via `x = 2t − 1`.
 -/

open Set intervalIntegral MeasureTheory Filter Topology Real

namespace RHDilog0514
open RHLeg0503

lemma int_pow_log (m : ℕ) : ∫ t in (0:ℝ)..1, t ^ m * Real.log t = -1 / ((m:ℝ) + 1) ^ 2 := by
  have hm : ((m:ℝ) + 1) ≠ 0 := by positivity
  set G : ℝ → ℝ := fun t => t ^ (m + 1) * Real.log t / ((m:ℝ) + 1) - t ^ (m + 1) / ((m:ℝ) + 1) ^ 2
    with hG
  have hG' : G = fun t => t ^ m * (t * Real.log t) / ((m:ℝ) + 1) - t ^ (m + 1) / ((m:ℝ) + 1) ^ 2 := by
    funext t; simp only [hG]; ring
  have hc : Continuous G := by
    rw [hG']
    exact (((continuous_pow m).mul Real.continuous_mul_log).div_const _).sub
      ((continuous_pow (m + 1)).div_const _)
  have hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt G (t ^ m * Real.log t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have h := (((hasDerivAt_pow (m + 1) t).mul (Real.hasDerivAt_log ht0)).div_const ((m:ℝ) + 1)).sub
      ((hasDerivAt_pow (m + 1) t).div_const (((m:ℝ) + 1) ^ 2))
    convert h using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ => t ^ m * Real.log t) volume 0 1 :=
    intervalIntegrable_log'.continuousOn_mul (continuous_pow m).continuousOn
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc.continuousOn hd hi]
  simp only [hG]
  simp
  field_simp

lemma term (n : ℕ) :
    ∫ t in (0:ℝ)..1, -Real.log t * (t ^ (n + 1) / ((n:ℝ) + 1)) =
      1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2) := by
  have h := int_pow_log (n + 1)
  have e : ∫ t in (0:ℝ)..1, -Real.log t * (t ^ (n + 1) / ((n:ℝ) + 1)) =
      (∫ t in (0:ℝ)..1, t ^ (n + 1) * Real.log t) * (-1 / ((n:ℝ) + 1)) := by
    rw [← intervalIntegral.integral_mul_const]; congr 1; funext t; ring
  have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n:ℝ) + 2) ≠ 0 := by positivity
  rw [e, h]; push_cast; field_simp; ring

/-- partial sums of `−log(1−t)` -/
noncomputable def S (N : ℕ) (t : ℝ) : ℝ := ∑ n ∈ Finset.range N, t ^ (n + 1) / ((n:ℝ) + 1)

lemma S_cont (N : ℕ) : Continuous (S N) := by
  unfold S; fun_prop

lemma f_ii (N : ℕ) : IntervalIntegrable (fun t => -Real.log t * S N t) volume 0 1 :=
  intervalIntegrable_log'.neg.mul_continuousOn (S_cont N).continuousOn

lemma S_int (N : ℕ) : ∫ t in (0:ℝ)..1, -Real.log t * S N t =
    ∑ n ∈ Finset.range N, 1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2) := by
  simp only [S, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · exact Finset.sum_congr rfl (fun n _ => term n)
  · intro n _
    exact intervalIntegrable_log'.neg.mul_continuousOn (by fun_prop)

lemma psum (N : ℕ) : ∑ n ∈ Finset.range N, 1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2) =
    2 - 1 / ((N:ℝ) + 1) - ∑ k ∈ Finset.range (N + 2), 1 / (k:ℝ) ^ 2 := by
  induction N with
  | zero => norm_num [Finset.sum_range_succ]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show N + 1 + 2 = (N + 2) + 1 by ring, Finset.sum_range_succ _ (N + 2)]
    push_cast
    have h1 : ((N:ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N:ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((N:ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma lim_psum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2))
    atTop (𝓝 (2 - π ^ 2 / 6)) := by
  have e : (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2)) =
      fun N : ℕ => 2 - 1 / ((N:ℝ) + 1) - ∑ k ∈ Finset.range (N + 2), 1 / (k:ℝ) ^ 2 := funext psum
  rw [e]
  have h1 : Tendsto (fun N : ℕ => 1 / ((N:ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 2), 1 / (k:ℝ) ^ 2) atTop (𝓝 (π ^ 2 / 6)) :=
    hasSum_zeta_two.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  have := ((tendsto_const_nhds (x := (2:ℝ))).sub h1).sub h2
  simpa using this

lemma F_bound (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ‖Real.log t * Real.log (1 - t)‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h; simp
  have ht0 : 0 < t := ht.1
  have h1t : 0 < 1 - t := by linarith
  have ha : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
  have hb : Real.log (1 - t) ≤ 0 := Real.log_nonpos h1t.le (by linarith)
  have ha' : -Real.log t ≤ (1 - t) / t := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 ht0)
    rw [Real.log_inv] at this
    have e : (1 - t) / t = t⁻¹ - 1 := by field_simp
    rw [e]; exact this
  have hb' : -Real.log (1 - t) ≤ t / (1 - t) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 h1t)
    rw [Real.log_inv] at this
    have e : t / (1 - t) = (1 - t)⁻¹ - 1 := by field_simp; ring
    rw [e]; exact this
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  calc Real.log t * Real.log (1 - t) = (-Real.log t) * (-Real.log (1 - t)) := by ring
    _ ≤ ((1 - t) / t) * (t / (1 - t)) :=
        mul_le_mul ha' hb' (by linarith) (div_nonneg h1t.le ht0.le)
    _ = 1 := by field_simp

lemma F_int : IntegrableOn (fun t : ℝ => Real.log t * Real.log (1 - t)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact (Real.measurable_log.mul (Real.measurable_log.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · exact ae_restrict_of_forall_mem measurableSet_Ioc F_bound

lemma F_ii : IntervalIntegrable (fun t : ℝ => Real.log t * Real.log (1 - t)) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 F_int

theorem dilog : ∫ t in (0:ℝ)..1, Real.log t * Real.log (1 - t) = 2 - π ^ 2 / 6 := by
  have hmct : Tendsto (fun N => ∫ t in Ioc (0:ℝ) 1, -Real.log t * S N t) atTop
      (𝓝 (∫ t in Ioc (0:ℝ) 1, Real.log t * Real.log (1 - t))) := by
    refine integral_tendsto_of_tendsto_of_monotone (fun N => (f_ii N).1) F_int ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      refine monotone_nat_of_le_succ (fun N => ?_)
      simp only [S, Finset.sum_range_succ, mul_add]
      have : 0 ≤ -Real.log t * (t ^ (N + 1) / ((N:ℝ) + 1)) :=
        mul_nonneg (by linarith [Real.log_nonpos ht.1.le ht.2]) (by have := ht.1; positivity)
      linarith
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h; simp
      have habs : |t| < 1 := by rw [abs_of_pos ht.1]; exact h
      have hs := (hasSum_pow_div_log_of_abs_lt_one habs).tendsto_sum_nat
      have := hs.const_mul (-Real.log t)
      have e : -Real.log t * -Real.log (1 - t) = Real.log t * Real.log (1 - t) := by ring
      rw [e] at this
      exact this
  have hval : (fun N => ∫ t in Ioc (0:ℝ) 1, -Real.log t * S N t) =
      fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (((n:ℝ) + 1) * ((n:ℝ) + 2) ^ 2) := by
    funext N; rw [← S_int N, intervalIntegral.integral_of_le zero_le_one]
  rw [hval] at hmct
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact tendsto_nhds_unique hmct lim_psum

lemma log_int01 : ∫ t in (0:ℝ)..1, Real.log t = -1 := by
  rw [integral_log]; simp

lemma log1m_int01 : ∫ t in (0:ℝ)..1, Real.log (1 - t) = -1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => Real.log x) 1]
  simp only [sub_self, sub_zero]
  exact log_int01

lemma log1m_ii01 : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume 0 1 := by
  have h := (intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
  norm_num at h; exact h

theorem kappa_zero : ∫ x in (-1:ℝ)..1, Real.log (1 + x) * Real.log (1 - x) * p 0 x =
    2 * Real.log 2 ^ 2 - 4 * Real.log 2 + 4 - π ^ 2 / 3 := by
  simp only [p_zero, mul_one]
  have hs : ∫ x in (-1:ℝ)..1, Real.log (1 + x) * Real.log (1 - x) =
      2 * ∫ t in (0:ℝ)..1, Real.log (1 + (2 * t - 1)) * Real.log (1 - (2 * t - 1)) := by
    rw [intervalIntegral.integral_comp_mul_sub (f := fun u : ℝ => Real.log (1 + u) * Real.log (1 - u))
      (by norm_num : (2:ℝ) ≠ 0) 1]
    simp only [smul_eq_mul]
    norm_num
    ring
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]; simp
  have hc : ∫ t in (0:ℝ)..1, Real.log (1 + (2 * t - 1)) * Real.log (1 - (2 * t - 1)) =
      ∫ t in (0:ℝ)..1, (Real.log 2 ^ 2 + Real.log 2 * Real.log (1 - t) + Real.log 2 * Real.log t) +
        Real.log t * Real.log (1 - t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 - t := lt_of_le_of_ne (by linarith [ht.2]) (by intro h; apply ht1; linarith)
    rw [show 1 + (2 * t - 1) = 2 * t by ring, show 1 - (2 * t - 1) = 2 * (1 - t) by ring,
      Real.log_mul (by norm_num) ht0.ne', Real.log_mul (by norm_num) h1t.ne']
    ring
  have i1 : IntervalIntegrable (fun t : ℝ => Real.log 2 ^ 2 + Real.log 2 * Real.log (1 - t)) volume 0 1 :=
    intervalIntegrable_const.add (log1m_ii01.const_mul _)
  have i2 : IntervalIntegrable (fun t : ℝ => Real.log 2 * Real.log t) volume 0 1 :=
    intervalIntegrable_log'.const_mul _
  rw [hs, hc, intervalIntegral.integral_add (i1.add i2) F_ii, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_add intervalIntegrable_const (log1m_ii01.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, log1m_int01, log_int01,
    dilog]
  simp
  ring

end RHDilog0514
