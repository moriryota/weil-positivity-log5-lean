import LamCore0522

open MeasureTheory Set Finset
open scoped BigOperators
namespace RHLamAnalytic0522
open RHLeg0503 RHLamCore0522

noncomputable def tay (κ : ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ range R, co κ r * t^(r+1)

lemma co_term (κ t : ℝ) (r : ℕ) :
    co κ r * t^(r+1) = - ((-(κ*t))^(r+1) / (r+1)) := by
  rcases Nat.even_or_odd r with he | ho
  · simp only [co, Nat.even_iff.mp he, ite_true, pow_succ, he.neg_pow, mul_pow]
    ring
  · simp only [co, Nat.odd_iff.mp ho, show ¬ (1:ℕ) = 0 by decide, ite_false,
      pow_succ, ho.neg_pow, mul_pow]
    ring

lemma tay_cont (κ : ℝ) (R : ℕ) : Continuous (tay κ R) := by
  unfold tay
  exact continuous_finsetSum _ (fun r _ => by fun_prop)

lemma log_contOn {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) :
    ContinuousOn (fun t => Real.log (1+κ*t)) (Icc (-1) 1) := by
  refine (by fun_prop : Continuous (fun t : ℝ => 1+κ*t)).continuousOn.log ?_
  intro t ht
  have h := mul_le_mul_of_nonneg_left ht.1 h0
  have : 0 < 1+κ*t := by nlinarith
  exact this.ne'

lemma log_p_ii {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (l : ℕ) :
    IntervalIntegrable (fun t => Real.log (1+κ*t) * p l t) volume (-1) 1 :=
  ((log_contOn h0 h1).mul (continuous_p l).continuousOn).intervalIntegrable_of_Icc (by norm_num)

lemma tay_error {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (R : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |Real.log (1+κ*t) - tay κ R t| ≤ κ^(R+1)/(1-κ) := by
  have hb : |-(κ*t)| ≤ κ := by
    rw [abs_neg, abs_mul, abs_of_nonneg h0]
    nlinarith
  have h := Real.abs_log_sub_add_sum_range_le (hb.trans_lt h1) R
  have he : tay κ R t = -(∑ r ∈ range R, (-(κ*t))^(r+1)/(r+1)) := by
    simp only [tay, co_term, sum_neg_distrib]
  rw [he]
  have he' : 1 - -(κ*t) = 1+κ*t := by ring
  rw [he'] at h
  have hd : 0 < 1 - |-(κ*t)| := by linarith
  have hK : 0 < 1-κ := by linarith
  calc
    _ = |(∑ r ∈ range R, (-(κ*t))^(r+1)/(r+1)) + Real.log (1+κ*t)| := by congr 1; ring
    _ ≤ |-(κ*t)|^(R+1)/(1-|-(κ*t)|) := h
    _ ≤ κ^(R+1)/(1-κ) := div_le_div₀ (pow_nonneg h0 _) (pow_le_pow_left₀ (abs_nonneg _) hb _) hK (by linarith)

lemma integral_tay (κ : ℝ) (R l : ℕ) :
    (∫ t in (-1:ℝ)..1, tay κ R t * p l t) = approx κ R l := by
  have he : (fun t => tay κ R t * p l t) =
      fun t => ∑ r ∈ range R, co κ r * (p l t * t^(r+1)) := by
    funext t
    simp only [tay, sum_mul]
    exact sum_congr rfl (fun r _ => by ring)
  rw [he, intervalIntegral.integral_finsetSum (f := fun r t => co κ r * (p l t * t^(r+1))) (fun r _ =>
    (continuous_const.mul ((continuous_p l).mul (continuous_pow (r+1)))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, RHCcSs0510.int_p_pow]
  unfold approx acc
  rw [mul_sum]
  exact sum_congr rfl (fun r _ => by ring)

/-- Uniform integrated Taylor remainder for every row index and truncation order. -/
theorem approx_error {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (R l : ℕ) :
    |RHRec2D0515.Mw (fun t => Real.log (1+κ*t)) 0 l - approx κ R l| ≤
      2*κ^(R+1)/(1-κ) := by
  unfold RHRec2D0515.Mw
  simp only [p_zero, one_mul]
  rw [← integral_tay κ R l, ← intervalIntegral.integral_sub (f := fun t => Real.log (1+κ*t) * p l t)
    (g := fun t => tay κ R t * p l t) (log_p_ii h0 h1 l)
    (((tay_cont κ R).mul (continuous_p l)).intervalIntegrable _ _)]
  have hB : 0 ≤ κ^(R+1)/(1-κ) := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -1) (b := 1)
    (f := fun t => Real.log (1+κ*t) * p l t - tay κ R t * p l t)
    (g := fun _ => κ^(R+1)/(1-κ)) (by norm_num)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
      calc
        _ ≤ (κ^(R+1)/(1-κ))*1 := mul_le_mul (tay_error h0 h1 R ht')
          (RHLegendreBound0520.abs_p_le_one l ht') (abs_nonneg _) hB
        _ = _ := mul_one _)) (intervalIntegrable_const)
  rw [Real.norm_eq_abs] at h
  convert h using 1 <;> simp [intervalIntegral.integral_const, smul_eq_mul] <;> ring

end RHLamAnalytic0522
