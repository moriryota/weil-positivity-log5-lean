import Leg0503
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # 0508: logarithmic Legendre moments

`μ_m = ∫_{−1}^1 log(1+x) P_m(x) dx`:
* `μ_0 = 2 log 2 − 2`,
* `μ_{n+1} = 2(−1)^{n+2}/((n+1)(n+2))`.
Proof: `F(x) = log(1+x)(x P_m − P_{m−1})/(m+1) = (1+x)log(1+x)·(x−1)P'_m/(m(m+1))` is continuous on
[−1,1], `F' = log(1+x) P_m + (x−1)P'_m/(m(m+1))` on (−1,1), `F(±1) = 0`. -/

open Set intervalIntegral

namespace RHLogMoment0508
open RHLeg0503

lemma log1p_ii : IntervalIntegrable (fun x : ℝ => Real.log (1 + x)) MeasureTheory.volume (-1) 1 := by
  have h := (intervalIntegrable_log' (a := 0) (b := 2)).comp_add_right 1
  simp only [zero_sub, show (2:ℝ) - 1 = 1 by norm_num] at h
  convert h using 2; ring

theorem mu_zero : ∫ x in (-1:ℝ)..1, Real.log (1 + x) * p 0 x = 2 * Real.log 2 - 2 := by
  simp only [p_zero, mul_one]
  have hc : ContinuousOn (fun x : ℝ => (1 + x) * Real.log (1 + x) - (1 + x)) (Icc (-1) 1) :=
    ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).sub
      (continuous_const.add continuous_id)).continuousOn
  have hd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x) - (1 + x))
      (Real.log (1 + x)) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have hl := ((hasDerivAt_id' x).const_add 1).log h1.ne'
    have h := ((((hasDerivAt_id' x).const_add 1).mul hl).sub ((hasDerivAt_id' x).const_add 1))
    convert h using 1; field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd log1p_ii]
  norm_num

theorem mu_succ (n : ℕ) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) * p (n + 1) x = 2 * (-1) ^ (n + 2) / ((n + 1) * (n + 2)) := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  set F : ℝ → ℝ := fun x => ((1 + x) * Real.log (1 + x)) * ((x - 1) * d (n + 1) x) / ((n + 1) * (n + 2)) with hF
  -- alternative form of F
  have hFalt : ∀ x, F x = Real.log (1 + x) * (x * p (n + 1) x - p n x) / (n + 1 + 1) := by
    intro x
    have h2 := (legS x n).2
    push_cast at h2
    rw [hF]; simp only
    linear_combination (norm := skip) (Real.log (1 + x) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * h2
    field_simp
    ring
  have hc : ContinuousOn F (Icc (-1) 1) := by
    apply Continuous.continuousOn
    rw [hF]
    exact ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).mul
      ((continuous_id.sub continuous_const).mul
        (continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt)))).div_const _
  have hd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F
      (Real.log (1 + x) * p (n + 1) x + (x - 1) * d (n + 1) x / ((n + 1) * (n + 2))) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have hl := ((hasDerivAt_id' x).const_add 1).log h1.ne'
    have hq := ((hasDerivAt_id' x).mul (hasDerivAt_p (n + 1) x)).sub (hasDerivAt_p n x)
    have h := (hl.mul hq).div_const ((n : ℝ) + 1 + 1)
    have hFe : F = fun x => Real.log (1 + x) * (x * p (n + 1) x - p n x) / (n + 1 + 1) := funext hFalt
    rw [hFe]
    convert h using 1
    obtain ⟨s1, s2⟩ := legS x n
    push_cast at s1 s2
    have hx1 : (1 + x) ≠ 0 := h1.ne'
    linear_combination (norm := skip) (-(Real.log (1 + x)) / ((n : ℝ) + 2)) * s1 +
      (1 / ((1 + x) * ((n : ℝ) + 1) * ((n : ℝ) + 2))) * s2
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun x => Real.log (1 + x) * p (n + 1) x + (x - 1) * d (n + 1) x / ((n + 1) * (n + 2)))
      MeasureTheory.volume (-1) 1 := by
    refine (log1p_ii.mul_continuousOn (continuous_p (n + 1)).continuousOn).add ?_
    have : Continuous fun x => (x - 1) * d (n + 1) x / ((n + 1) * (n + 2)) :=
      ((continuous_id.sub continuous_const).mul
        (continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt))).div_const _
    exact this.intervalIntegrable _ _
  have hftc := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd hint
  have hF1 : F 1 = 0 := by rw [hFalt, p_at_one, p_at_one]; ring
  have hFm1 : F (-1) = 0 := by rw [hF]; simp
  rw [hF1, hFm1, sub_zero] at hftc
  -- split the integral
  have hpc : Continuous fun x => (x - 1) * d (n + 1) x / ((n + 1) * (n + 2)) :=
    ((continuous_id.sub continuous_const).mul
      (continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt))).div_const _
  rw [integral_add (log1p_ii.mul_continuousOn (continuous_p (n + 1)).continuousOn) (hpc.intervalIntegrable _ _),
    integral_div] at hftc
  -- ∫ (x−1) P'_m = 2 (−1)^m
  have hG : ∫ x in (-1:ℝ)..1, (p (n + 1) x + (x - 1) * d (n + 1) x) = 0 * p (n + 1) 1 - (-1 - 1) * p (n + 1) (-1) := by
    have hd2 : ∀ x ∈ Set.uIcc (-1:ℝ) 1, HasDerivAt (fun x => (x - 1) * p (n + 1) x)
        (p (n + 1) x + (x - 1) * d (n + 1) x) x := by
      intro x _
      have h := ((hasDerivAt_id' x).sub_const 1).mul (hasDerivAt_p (n + 1) x)
      convert h using 1; ring
    rw [integral_eq_sub_of_hasDerivAt hd2 (((continuous_p _).add ((continuous_id.sub continuous_const).mul
      (continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt)))).intervalIntegrable _ _)]
    ring
  have hP : ∫ x in (-1:ℝ)..1, p (n + 1) x = 0 := by
    rw [integral_left_succ, p_at_one, p_at_one]; ring
  have hsplit : (∫ x in (-1:ℝ)..1, (p (n + 1) x + (x - 1) * d (n + 1) x)) =
      (∫ x in (-1:ℝ)..1, p (n + 1) x) + ∫ x in (-1:ℝ)..1, (x - 1) * d (n + 1) x :=
    integral_add (f := fun x => p (n + 1) x) (g := fun x => (x - 1) * d (n + 1) x)
      ((continuous_p _).intervalIntegrable _ _) (((continuous_id.sub continuous_const).mul
      (continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt))).intervalIntegrable _ _)
  rw [hsplit, hP, zero_add, p_at_neg_one] at hG
  rw [hG] at hftc
  field_simp at hftc ⊢
  rw [pow_succ] at hftc ⊢
  linear_combination hftc

end RHLogMoment0508

