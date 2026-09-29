import Kappa0514
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # 0514: the moment `∫ log²(1+x) P_m` for `m ≥ 1`

`y ↦ y log² y` is continuous on `[0,∞)`; with `F(x) = (1+x)log²(1+x)·(x−1)P'_m/(m(m+1))`,
`∫_{−1}^1 log²(1+x) P_m = −(2/(m(m+1))) ∫_{−1}^1 log(1+x)(x−1)P'_m`. -/

open Set intervalIntegral Filter Topology

namespace RHNu0514
open RHLeg0503 RHLogMoment0508 RHKappa0514

lemma ylog2_contOn : ContinuousOn (fun y : ℝ => y * Real.log y ^ 2) (Ici 0) := by
  intro y hy
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y from hy) with h0 | hpos
  · subst h0
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have ht := tendsto_log_mul_rpow_nhdsGT_zero (r := 1/2) (by norm_num)
    have h2 := ht.pow 2
    simp only [zero_pow (two_ne_zero), zero_mul] at h2 ⊢
    unfold ContinuousWithinAt
    simp only [zero_mul]
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have : (x ^ ((1:ℝ)/2)) ^ 2 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [mul_pow, this]; ring
  · exact ((continuous_id.continuousAt).mul ((Real.continuousAt_log hpos.ne').pow 2)).continuousWithinAt

noncomputable def Λ (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) ^ 2 - 2 * ((1 + x) * Real.log (1 + x)) + 2 * (1 + x)

lemma Λ_cont : ContinuousOn Λ (Icc (-1) 1) := by
  unfold Λ
  have hg : ContinuousOn (fun x : ℝ => (1 + x) * Real.log (1 + x) ^ 2) (Icc (-1) 1) :=
    ylog2_contOn.comp (continuous_const.add continuous_id).continuousOn
      (fun x hx => show (0:ℝ) ≤ 1 + x by linarith [hx.1])
  have h2 : Continuous fun x : ℝ => 2 * ((1 + x) * Real.log (1 + x)) :=
    continuous_const.mul (Real.continuous_mul_log.comp (continuous_const.add continuous_id))
  have h3 : Continuous fun x : ℝ => 2 * (1 + x) := continuous_const.mul (continuous_const.add continuous_id)
  exact (hg.sub h2.continuousOn).add h3.continuousOn

lemma Λ_deriv (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) : HasDerivAt Λ (Real.log (1 + x) ^ 2) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have hl := ((hasDerivAt_id' x).const_add 1).log h1.ne'
  have ha := ((hasDerivAt_id' x).const_add 1)
  have h := ((ha.mul (hl.pow 2)).sub ((ha.mul hl).const_mul 2)).add (ha.const_mul 2)
  unfold Λ
  convert h using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma log2_ii : IntervalIntegrable (fun x : ℝ => Real.log (1 + x) ^ 2) MeasureTheory.volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact integrableOn_deriv_of_nonneg Λ_cont Λ_deriv (fun x _ => sq_nonneg _)

theorem nu_zero : ∫ x in (-1:ℝ)..1, Real.log (1 + x) ^ 2 * p 0 x = 2 * Real.log 2 ^ 2 - 4 * Real.log 2 + 4 := by
  simp only [p_zero, mul_one]
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) Λ_cont Λ_deriv log2_ii]
  unfold Λ; norm_num; ring

theorem nu_succ (n : ℕ) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) ^ 2 * p (n + 1) x =
      -(2 * ∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x - 1) * d (n + 1) x)) / ((n + 1) * (n + 2)) := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  set F : ℝ → ℝ := fun x => ((1 + x) * Real.log (1 + x) ^ 2) * ((x - 1) * d (n + 1) x) / ((n + 1) * (n + 2)) with hF
  have hFalt : ∀ x, F x = Real.log (1 + x) ^ 2 * (x * p (n + 1) x - p n x) / (n + 1 + 1) := by
    intro x
    have h2 := (legS x n).2
    push_cast at h2
    rw [hF]; simp only
    linear_combination (norm := skip) (Real.log (1 + x) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * h2
    field_simp
    ring
  have hc : ContinuousOn F (Icc (-1) 1) := by
    rw [hF]
    have hg : ContinuousOn (fun x : ℝ => (1 + x) * Real.log (1 + x) ^ 2) (Icc (-1) 1) :=
      ylog2_contOn.comp (continuous_const.add continuous_id).continuousOn
        (fun x hx => show (0:ℝ) ≤ 1 + x by linarith [hx.1])
    exact (hg.mul ((continuous_id.sub continuous_const).mul (dcont (n + 1))).continuousOn).div_const _
  have hd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F
      (Real.log (1 + x) ^ 2 * p (n + 1) x + 2 * (Real.log (1 + x) * ((x - 1) * d (n + 1) x)) / ((n + 1) * (n + 2))) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have hl1 := (((hasDerivAt_id' x).const_add 1).log h1.ne').pow 2
    have hq := ((hasDerivAt_id' x).mul (hasDerivAt_p (n + 1) x)).sub (hasDerivAt_p n x)
    have h := (hl1.mul hq).div_const ((n : ℝ) + 1 + 1)
    have hFe : F = fun x => Real.log (1 + x) ^ 2 * (x * p (n + 1) x - p n x) / (n + 1 + 1) := funext hFalt
    rw [hFe]
    convert h using 1
    obtain ⟨s1, s2⟩ := legS x n
    push_cast at s1 s2
    have hx1 : (1 + x) ≠ 0 := h1.ne'
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    linear_combination (norm := skip)
      (-(Real.log (1 + x) ^ 2) / ((n : ℝ) + 2)) * s1 +
      ((2 * Real.log (1 + x)) / ((1 + x) * ((n : ℝ) + 1) * ((n : ℝ) + 2))) * s2
    field_simp
    ring
  have iA : IntervalIntegrable (fun x => Real.log (1 + x) ^ 2 * p (n + 1) x) MeasureTheory.volume (-1) 1 :=
    log2_ii.mul_continuousOn (continuous_p _).continuousOn
  have hc1 : Continuous fun x => (x - 1) * d (n + 1) x := (continuous_id.sub continuous_const).mul (dcont _)
  have iB : IntervalIntegrable (fun x => Real.log (1 + x) * ((x - 1) * d (n + 1) x)) MeasureTheory.volume (-1) 1 :=
    log1p_ii.mul_continuousOn hc1.continuousOn
  have hint := iA.add ((iB.const_mul 2).div_const (((n : ℝ) + 1) * ((n : ℝ) + 2)))
  have hftc := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd hint
  have hF1 : F 1 = 0 := by rw [hF]; simp
  have hFm1 : F (-1) = 0 := by rw [hF]; simp
  rw [hF1, hFm1, sub_zero] at hftc
  rw [integral_add iA ((iB.const_mul 2).div_const _), integral_div, integral_const_mul] at hftc
  have hden : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp at hftc ⊢
  linarith

end RHNu0514

