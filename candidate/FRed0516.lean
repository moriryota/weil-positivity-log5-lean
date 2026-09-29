import AffRed0516

/-! # 0516: affine reduction of `F i k s = ∫_{s−1}^1 lg(u) P_i(u) P_k(u−s) du` (0 < s < 2)

With `b = 1 − s/2`, `a = s/2`, `κ = b/(1+a)`, `A = Af b a i`, `B = Af b (a−s) k`:
`F = b[(log b + log(1+a)) Σ_j A_j B_j 2/(2j+1) + Σ_j Σ_j' A_j B_j' ((−1)^{j+j'} M⁺_{jj'} + Mκ_{jj'})]`.
 -/

open Set MeasureTheory intervalIntegral Finset

namespace RHFRed0516
open RHLeg0503 RHLegVec0503 RHSingDef0516 RHPairInt0516 RHPrAff0511 RHRec2D0515 RHAffRed0516

lemma Mw_refl (j j' : ℕ) : Mw (fun t => Real.log (1 - t)) j j' = (-1) ^ (j + j') * Mw (fun t => Real.log (1 + t)) j j' := by
  show ∫ x in (-1:ℝ)..1, Real.log (1 - x) * (p j x * p j' x) =
    (-1) ^ (j + j') * ∫ x in (-1:ℝ)..1, Real.log (1 + x) * (p j x * p j' x)
  have h := refl (a := -1) (b := 1) (fun t => Real.log (1 + t) * (p j t * p j' t))
  norm_num at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; funext t
  have hs : ((-1:ℝ) ^ (j + j')) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨j + j', by ring⟩
  rw [show 1 + -t = 1 - t by ring, p_neg, p_neg]
  linear_combination (-(Real.log (1 - t) * (p j t * p j' t))) * hs

lemma logk_ii {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) :
    IntervalIntegrable (fun t => Real.log (1 + κ * t)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.log (by fun_prop)
  intro t ht
  rw [Set.uIcc_of_le (by norm_num)] at ht
  have : -κ ≤ κ * t := by nlinarith [ht.1]
  linarith

theorem F_eq (i k : ℕ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    F i k s = (1 - s / 2) * ((Real.log (1 - s / 2) + Real.log (1 + s / 2)) *
        ∑ j ∈ range (i + 1), Af (1 - s / 2) (s / 2) i j * Af (1 - s / 2) (s / 2 - s) k j * (2 / (2 * j + 1)) +
      ∑ j ∈ range (i + 1), ∑ j' ∈ range (k + 1), Af (1 - s / 2) (s / 2) i j * Af (1 - s / 2) (s / 2 - s) k j' *
        ((-1) ^ (j + j') * Mw (fun t => Real.log (1 + t)) j j' +
          Mw (fun t => Real.log (1 + (1 - s / 2) / (1 + s / 2) * t)) j j')) := by
  set b := 1 - s / 2 with hb
  set a := s / 2 with ha
  set κ := b / (1 + a) with hκ
  have hb0 : 0 < b := by rw [hb]; linarith
  have ha0 : 0 < 1 + a := by rw [ha]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one ha0, hb, ha]; linarith
  unfold F
  rw [aff_sub (by linarith)]
  have e1 : (1 - (s - 1)) / 2 = b := by rw [hb]; ring
  have e2 : (s - 1 + 1) / 2 = a := by rw [ha]; ring
  rw [e1, e2]
  congr 1
  have hc : Continuous fun t => p i (b * t + a) * p k (b * t + (a - s)) :=
    ((continuous_p i).comp (by fun_prop)).mul ((continuous_p k).comp (by fun_prop))
  have iC := (hc.intervalIntegrable (μ := volume) (-1) 1).const_mul (Real.log b + Real.log (1 + a))
  have iM := RHKappa0514.log1m_ii.mul_continuousOn hc.continuousOn
  have iK := (logk_ii hκ0 hκ1).mul_continuousOn hc.continuousOn
  have hpt : ∫ t in (-1:ℝ)..1, lg (b * t + a) * p i (b * t + a) * p k (b * t + a - s) =
      ∫ t in (-1:ℝ)..1, ((Real.log b + Real.log (1 + a)) * (p i (b * t + a) * p k (b * t + (a - s))) +
        Real.log (1 - t) * (p i (b * t + a) * p k (b * t + (a - s))) +
        Real.log (1 + κ * t) * (p i (b * t + a) * p k (b * t + (a - s)))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume 1] with t hne ht
    rw [uIoc_of_le (by norm_num)] at ht
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 hne
    have hκt : 0 < 1 + κ * t := by nlinarith [ht.1]
    have hu1 : -1 < b * t + a := by rw [hb, ha]; nlinarith [ht.1]
    have hu2 : b * t + a < 1 := by rw [hb, ha]; nlinarith
    rw [lg_eq hu1 hu2]
    have f1 : 1 - (b * t + a) = b * (1 - t) := by rw [hb, ha]; ring
    have f2 : 1 + (b * t + a) = (1 + a) * (1 + κ * t) := by rw [hκ]; field_simp; ring
    rw [f1, f2, Real.log_mul hb0.ne' (by linarith), Real.log_mul ha0.ne' hκt.ne',
      show b * t + a - s = b * t + (a - s) by ring]
    ring
  rw [hpt, intervalIntegral.integral_add (iC.add iM) iK, intervalIntegral.integral_add iC iM,
    intervalIntegral.integral_const_mul, aff_int, wbil _ RHKappa0514.log1m_ii, wbil _ (logk_ii hκ0 hκ1)]
  simp only [Mw_refl]
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun j' _ => ?_)
  ring

end RHFRed0516

