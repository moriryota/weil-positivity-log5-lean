import GammaExp0516

/-! # 0516: full expansion of `γ_ik = ∫_{−1}^1 φ_i φ_k`

`γ = ¼((1+e) N_ik + 2 K_ik) + ½ (1+e) Σ_a w_a (F i k s_a + F k i s_a)
     + (1+e) Σ_{a,b} w_a w_b OO i k s_a s_b + w_2² (X i k s_2 s_2 + X k i s_2 s_2)`,
`e = (−1)^{i+k}`, `s_a = σ_{2,3,4}`, `N = Mw log²(1+x)`, `K = Mw log(1+x)log(1−x)`. -/

open Set MeasureTheory intervalIntegral Finset

namespace RHGammaFull0516
open RHLeg0503 RHSingDef0516 RHPairInt0516 RHGammaExp0516 RHLog5Bridge

/-! ### shifts -/

lemma sig_eq (m : ℕ) : σ m = 2 * Real.log m / Real.log 5 := by
  unfold σ halfWidth; field_simp

lemma log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

lemma sig_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ σ m := by
  rw [sig_eq]; apply div_nonneg _ log5_pos.le
  have : (1:ℝ) ≤ m := by exact_mod_cast hm
  linarith [Real.log_nonneg this]

lemma sig_le {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 5) : σ m ≤ 2 := by
  rw [sig_eq, div_le_iff₀ log5_pos]
  have : Real.log m ≤ Real.log 5 := Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hm)
  linarith

lemma sig_add (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    σ m + σ m' = 2 * Real.log ((m:ℝ) * m') / Real.log 5 := by
  rw [sig_eq, sig_eq, Real.log_mul (by positivity) (by positivity)]; ring

lemma sig_sum_le {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (h : m * m' ≤ 5) : σ m + σ m' ≤ 2 := by
  rw [sig_add m m' hm hm', div_le_iff₀ log5_pos]
  have : Real.log ((m:ℝ) * m') ≤ Real.log 5 :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  linarith

lemma sig_sum_ge {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (h : 5 ≤ m * m') : 2 ≤ σ m + σ m' := by
  rw [sig_add m m' hm hm', le_div_iff₀ log5_pos]
  have : Real.log 5 ≤ Real.log ((m:ℝ) * m') :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h)
  linarith

lemma Sh_bounds (a : Fin 3) : 0 ≤ Sh a ∧ Sh a ≤ 2 := by
  fin_cases a <;> simp [Sh] <;>
    exact ⟨sig_nonneg (by norm_num), sig_le (by norm_num) (by norm_num)⟩

/-! ### lg² -/

lemma log1m_sq_ii : IntervalIntegrable (fun u : ℝ => Real.log (1 - u) ^ 2) volume (-1) 1 := by
  have h := RHNu0514.log2_ii.comp_sub_left 0
  simp only [zero_sub, neg_neg, zero_add] at h
  exact h.symm.congr (fun u _ => by ring_nf)

theorem lgsq (i k : ℕ) :
    ∫ u in (-1:ℝ)..1, lg u ^ 2 * (p i u * p k u) =
      (1 + (-1) ^ (i + k)) * RHRec2D0515.Mw (fun x => Real.log (1 + x) ^ 2) i k +
        2 * RHRec2D0515.Mw (fun x => Real.log (1 + x) * Real.log (1 - x)) i k := by
  have hc : Continuous fun u => p i u * p k u := (continuous_p i).mul (continuous_p k)
  have i1 := RHNu0514.log2_ii.mul_continuousOn hc.continuousOn
  have i2 := (RHBaseNK0515.kw_ii.mul_continuousOn hc.continuousOn).const_mul 2
  have i3 := log1m_sq_ii.mul_continuousOn hc.continuousOn
  have e : ∫ u in (-1:ℝ)..1, lg u ^ 2 * (p i u * p k u) =
      ∫ u in (-1:ℝ)..1, (Real.log (1 + u) ^ 2 * (p i u * p k u) +
        2 * (Real.log (1 + u) * Real.log (1 - u) * (p i u * p k u)) +
        Real.log (1 - u) ^ 2 * (p i u * p k u)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [lg_ae] with u hu hu'
    rw [hu hu']; ring
  rw [e, intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul]
  have hr : ∫ u in (-1:ℝ)..1, Real.log (1 - u) ^ 2 * (p i u * p k u) =
      (-1) ^ (i + k) * ∫ u in (-1:ℝ)..1, Real.log (1 + u) ^ 2 * (p i u * p k u) := by
    have h := refl (a := -1) (b := 1) (fun u => Real.log (1 + u) ^ 2 * (p i u * p k u))
    norm_num at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    congr 1; funext u
    have hs : ((-1:ℝ) ^ (i + k)) ^ 2 = 1 := by
      rw [← pow_mul]; exact Even.neg_one_pow ⟨i + k, by ring⟩
    rw [show 1 + -u = 1 - u by ring, p_neg, p_neg]
    linear_combination (-(Real.log (1 - u) ^ 2 * (p i u * p k u))) * hs
  rw [hr]
  unfold RHRec2D0515.Mw
  simp only [mul_assoc]
  ring

end RHGammaFull0516

