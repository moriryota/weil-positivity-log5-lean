import LogMoment0508

/-! # 0514: the moment `∫ log(1+x) log(1−x) P_m` for `m ≥ 1`

With `F(x) = [(1+x)log(1+x)]·[(1−x)log(1−x)]·(−P'_m)/(m(m+1))` (continuous on [−1,1], `F(±1)=0`),
`∫_{−1}^1 log(1+x)log(1−x) P_m = −(∫ log(1−x)(x−1)P'_m + ∫ log(1+x)(x+1)P'_m)/(m(m+1))`.
 -/

open Set intervalIntegral

namespace RHKappa0514
open RHLeg0503 RHLogMoment0508

lemma log1m_ii : IntervalIntegrable (fun x : ℝ => Real.log (1 - x)) MeasureTheory.volume (-1) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 2) (b := 0)).comp_sub_left 1
  norm_num at h; exact h

lemma dcont (m : ℕ) : Continuous (d m) :=
  continuous_iff_continuousAt.mpr (fun x => (Polynomial.differentiable _ x).continuousAt)

theorem kappa_succ (n : ℕ) :
    ∫ x in (-1:ℝ)..1, Real.log (1 + x) * Real.log (1 - x) * p (n + 1) x =
      -((∫ x in (-1:ℝ)..1, Real.log (1 - x) * ((x - 1) * d (n + 1) x)) +
        ∫ x in (-1:ℝ)..1, Real.log (1 + x) * ((x + 1) * d (n + 1) x)) / ((n + 1) * (n + 2)) := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  set F : ℝ → ℝ := fun x => ((1 + x) * Real.log (1 + x)) * ((1 - x) * Real.log (1 - x)) *
    (-(d (n + 1) x)) / ((n + 1) * (n + 2)) with hF
  -- F = log(1+x) log(1−x) (x p_{n+1} − p_n)/(n+2)
  have hFalt : ∀ x, F x = Real.log (1 + x) * Real.log (1 - x) * (x * p (n + 1) x - p n x) / (n + 1 + 1) := by
    intro x
    have h2 := (legS x n).2
    push_cast at h2
    rw [hF]; simp only
    linear_combination (norm := skip) (Real.log (1 + x) * Real.log (1 - x) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * h2
    field_simp
    ring
  have hc : ContinuousOn F (Icc (-1) 1) := by
    apply Continuous.continuousOn
    rw [hF]
    exact ((((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).mul (dcont (n + 1)).neg).div_const _)
  have hd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F
      (Real.log (1 + x) * Real.log (1 - x) * p (n + 1) x +
        (Real.log (1 - x) * ((x - 1) * d (n + 1) x) + Real.log (1 + x) * ((x + 1) * d (n + 1) x)) / ((n + 1) * (n + 2))) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have h2 : 0 < 1 - x := by linarith [hx.2]
    have hl1 := ((hasDerivAt_id' x).const_add 1).log h1.ne'
    have hl2 := ((hasDerivAt_id' x).const_sub 1).log h2.ne'
    have hq := ((hasDerivAt_id' x).mul (hasDerivAt_p (n + 1) x)).sub (hasDerivAt_p n x)
    have h := ((hl1.mul hl2).mul hq).div_const ((n : ℝ) + 1 + 1)
    have hFe : F = fun x => Real.log (1 + x) * Real.log (1 - x) * (x * p (n + 1) x - p n x) / (n + 1 + 1) := funext hFalt
    rw [hFe]
    convert h using 1
    obtain ⟨s1, s2⟩ := legS x n
    push_cast at s1 s2
    have hx1 : (1 + x) ≠ 0 := h1.ne'
    have hx2 : (1 - x) ≠ 0 := h2.ne'
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (norm := skip)
      (-(Real.log (1 + x) * Real.log (1 - x)) / ((n : ℝ) + 2)) * s1 +
      ((Real.log (1 - x) / (1 + x) - Real.log (1 + x) / (1 - x)) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * s2
    field_simp
    ring
  -- integrability
  have hLL : IntervalIntegrable (fun x => Real.log (1 + x) * Real.log (1 - x)) MeasureTheory.volume (-1) 1 := by
    have hb : IntervalIntegrable (fun x => Real.log 2 * (|Real.log (1 + x)| + |Real.log (1 - x)|))
        MeasureTheory.volume (-1) 1 :=
      ((log1p_ii.norm).add (log1m_ii.norm)).const_mul (Real.log 2) |>.congr (fun x _ => by simp [Real.norm_eq_abs])
    refine hb.mono_fun ?_ ?_
    · exact ((Real.measurable_log.comp (measurable_const.add measurable_id)).mul
        (Real.measurable_log.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      rw [Set.uIoc_of_le (by norm_num)] at hx
      dsimp only
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hs : 0 ≤ |Real.log (1 + x)| + |Real.log (1 - x)| := by positivity
      rw [abs_of_nonneg (mul_nonneg hl2 hs)]
      rcases le_total x 0 with h0 | h0
      · have hb2 : |Real.log (1 - x)| ≤ Real.log 2 := by
          rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
          exact Real.log_le_log (by linarith) (by linarith [hx.1])
        nlinarith [abs_nonneg (Real.log (1 + x)), abs_nonneg (Real.log (1 - x))]
      · have hb1 : |Real.log (1 + x)| ≤ Real.log 2 := by
          rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
          exact Real.log_le_log (by linarith) (by linarith [hx.2])
        nlinarith [abs_nonneg (Real.log (1 + x)), abs_nonneg (Real.log (1 - x))]
  have hc1 : Continuous fun x => (x - 1) * d (n + 1) x := (continuous_id.sub continuous_const).mul (dcont _)
  have hc2 : Continuous fun x => (x + 1) * d (n + 1) x := (continuous_id.add continuous_const).mul (dcont _)
  have iA : IntervalIntegrable (fun x => Real.log (1 + x) * Real.log (1 - x) * p (n + 1) x) MeasureTheory.volume (-1) 1 :=
    hLL.mul_continuousOn (continuous_p _).continuousOn
  have iB : IntervalIntegrable (fun x => Real.log (1 - x) * ((x - 1) * d (n + 1) x)) MeasureTheory.volume (-1) 1 :=
    log1m_ii.mul_continuousOn hc1.continuousOn
  have iC : IntervalIntegrable (fun x => Real.log (1 + x) * ((x + 1) * d (n + 1) x)) MeasureTheory.volume (-1) 1 :=
    log1p_ii.mul_continuousOn hc2.continuousOn
  have hint := iA.add ((iB.add iC).div_const (((n : ℝ) + 1) * ((n : ℝ) + 2)))
  have hftc := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd hint
  have hF1 : F 1 = 0 := by rw [hF]; simp
  have hFm1 : F (-1) = 0 := by rw [hF]; simp
  rw [hF1, hFm1, sub_zero] at hftc
  rw [integral_add iA ((iB.add iC).div_const _), integral_div, integral_add iB iC] at hftc
  have hden : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp at hftc ⊢
  linarith

end RHKappa0514

