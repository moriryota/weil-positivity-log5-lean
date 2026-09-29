import FRed0516
import PrSum0511

/-! # 0516: the coefficients `s` and their link to the kernel-checked `Pr` (0511/0512)

* `∫_{−1}^1 φ_i P_k = ½(1+e) M⁺_ik + Σ_a W_a (1+e) OO i k s_a 0`;
* `Pr i k = L c_i c_k Σ_a W_a (1+e) OO i k s_a 0` (from 0511 `Pr_eq`, `Jm_eq` and `OO_eq`).
 -/

open Set MeasureTheory intervalIntegral Finset

namespace RHSRed0516
open RHLeg0503 RHSingDef0516 RHPairInt0516 RHGammaExp0516 RHGammaFull0516 RHAffRed0516 RHRec2D0515
  RHLog5Bridge RHPrAff0511

lemma lgp_eq (i k : ℕ) : ∫ u in (-1:ℝ)..1, lg u * p i u * p k u =
    (1 + (-1) ^ (i + k)) * Mw (fun t => Real.log (1 + t)) i k := by
  have hc : Continuous fun u => p i u * p k u := (continuous_p i).mul (continuous_p k)
  have i1 := RHLogMoment0508.log1p_ii.mul_continuousOn hc.continuousOn
  have i2 := RHKappa0514.log1m_ii.mul_continuousOn hc.continuousOn
  have e : ∫ u in (-1:ℝ)..1, lg u * p i u * p k u =
      ∫ u in (-1:ℝ)..1, (Real.log (1 + u) * (p i u * p k u) + Real.log (1 - u) * (p i u * p k u)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [lg_ae] with u hu hu'
    rw [hu hu']; ring
  rw [e, intervalIntegral.integral_add i1 i2]
  have h2 := RHFRed0516.Mw_refl i k
  unfold Mw at h2 ⊢
  simp only at h2 ⊢
  rw [h2]; ring

lemma pm0 (i k : ℕ) (s : ℝ) :
    ∫ u in (-1:ℝ)..1, pm i s u * p k u = ∫ u in (-1:ℝ)..1, pm i s u * pm k 0 u := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun u hu => ?_))
  rw [uIoc_of_le (by norm_num)] at hu
  have h : -1 < u := hu.1
  simp [pm, h]

lemma pp0 (i k : ℕ) (s : ℝ) :
    ∫ u in (-1:ℝ)..1, pp i s u * p k u = ∫ u in (-1:ℝ)..1, pp i s u * pp k 0 u := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun u hu => ?_))
  rw [uIoc_of_le (by norm_num)] at hu
  have h : u ≤ 1 := hu.2
  simp [pp, h]

lemma prp_term_ii (i k : ℕ) (a : Fin 3) :
    IntervalIntegrable (fun u => W a * (pm i (Sh a) u * p k u + pp i (Sh a) u * p k u)) volume (-1) 1 := by
  have h1 : IntervalIntegrable (fun u => pm i (Sh a) u * p k u) volume (-1) 1 := by
    simp only [pm_def]; exact ii_gt_mul (cont_ii ((cps i _).mul (continuous_p k))) _
  have h2 : IntervalIntegrable (fun u => pp i (Sh a) u * p k u) volume (-1) 1 := by
    simp only [pp_def]; exact ii_le_mul (cont_ii ((cpa i _).mul (continuous_p k))) _
  exact (h1.add h2).const_mul _

theorem phi_p (i k : ℕ) : ∫ u in (-1:ℝ)..1, phi i u * p k u =
    (1 / 2) * ((1 + (-1) ^ (i + k)) * Mw (fun t => Real.log (1 + t)) i k) +
      ∑ a : Fin 3, W a * ((1 + (-1) ^ (i + k)) * OO i k (Sh a) 0) := by
  have iA : IntervalIntegrable (fun u => (1 / 2) * (lg u * p i u * p k u)) volume (-1) 1 :=
    (lgp_ii i (p k) (continuous_p k)).const_mul _
  have iP : IntervalIntegrable (fun u => ∑ a : Fin 3, W a * (pm i (Sh a) u * p k u + pp i (Sh a) u * p k u))
      volume (-1) 1 :=
    (IntervalIntegrable.sum (Finset.univ) (f := fun a u => W a * (pm i (Sh a) u * p k u + pp i (Sh a) u * p k u))
      (fun a _ => prp_term_ii i k a)).congr (fun u _ => by simp [Finset.sum_apply])
  have e : (fun u => phi i u * p k u) = fun u => (1 / 2) * (lg u * p i u * p k u) +
      ∑ a : Fin 3, W a * (pm i (Sh a) u * p k u + pp i (Sh a) u * p k u) := by
    funext u; rw [phi, pr_sum, add_mul, sum_mul]; congr 1
    · ring
    · exact sum_congr rfl (fun a _ => by ring)
  rw [e, intervalIntegral.integral_add iA iP, intervalIntegral.integral_const_mul, lgp_eq,
    intervalIntegral.integral_finsetSum (fun a _ => prp_term_ii i k a)]
  congr 1
  refine sum_congr rfl (fun a _ => ?_)
  obtain ⟨a0, a2⟩ := Sh_bounds a
  have h1 : IntervalIntegrable (fun u => pm i (Sh a) u * p k u) volume (-1) 1 := by
    simp only [pm_def]; exact ii_gt_mul (cont_ii ((cps i _).mul (continuous_p k))) _
  have h2 : IntervalIntegrable (fun u => pp i (Sh a) u * p k u) volume (-1) 1 := by
    simp only [pp_def]; exact ii_le_mul (cont_ii ((cpa i _).mul (continuous_p k))) _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2, pm0, pp0,
    P1 i k a0 a2 (le_refl 0) (by norm_num), P2 i k a0 a2 (le_refl 0) (by norm_num)]
  ring

/-- `Jm` of 0511 in terms of `OO`. -/
lemma Jm_OO (i k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 5) :
    RHPrRed0511.Jm i k (Real.log m) = halfWidth * RHRpExact0506.cc i * RHRpExact0506.cc k * OO i k (σ m) 0 := by
  have hL := halfWidth_pos
  have hs0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hs2 : Real.log m < 2 * halfWidth := by
    rw [twice_halfWidth]; exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hm)
  have hσ0 : 0 ≤ σ m := sig_nonneg hm1
  have hσ2 : σ m < 2 := by unfold σ; rw [div_lt_iff₀ hL]; linarith
  rw [RHPrRed0511.Jm_eq i k hs0 hs2, OO_eq i k hσ2 (by norm_num : (0:ℝ) < 2), max_eq_left hσ0]
  have a1 : (1 - (σ m - 1)) / 2 = (2 - Real.log m / halfWidth) / 2 := by unfold σ; ring
  have a2 : (σ m - 1 + 1) / 2 - σ m = -(Real.log m / halfWidth) / 2 := by unfold σ; ring
  have a3 : (σ m - 1 + 1) / 2 - 0 = Real.log m / halfWidth / 2 := by unfold σ; ring
  rw [a1, a2, a3]
  ring

theorem Pr_OO (i k : ℕ) : RHColDecomp0499.Pr i k =
    halfWidth * RHRpExact0506.cc i * RHRpExact0506.cc k * ∑ a : Fin 3, W a * ((1 + (-1) ^ (i + k)) * OO i k (Sh a) 0) := by
  rw [RHPrSum0511.Pr_eq]
  have j2 := Jm_OO i k (m := 2) (by norm_num) (by norm_num)
  have j3 := Jm_OO i k (m := 3) (by norm_num) (by norm_num)
  have j4 := Jm_OO i k (m := 4) (by norm_num) (by norm_num)
  push_cast at j2 j3 j4
  rw [j2, j3, j4]
  simp only [Fin.sum_univ_three, W, Sh, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

end RHSRed0516

