import PairInt0516
import BaseNK0515

/-! # 0516: expansion of `γ_ik = ∫_{−1}^1 φ_i φ_k` into pair integrals

With `e = (−1)^{i+k}`, shifts `s_2, s_3, s_4 ∈ [0,2]`, `s_2 + s_2 ≤ 2` and all other pair sums `≥ 2`:
`γ = ¼ ∫lg² P_i P_k + ½ Σ_a w_a (1+e)(F i k s_a + F k i s_a) + (1+e) Σ_{a,b} w_a w_b OO i k s_a s_b
     + w_2² (X i k s_2 s_2 + X k i s_2 s_2)`,
and `∫ lg² P_i P_k = (1+e) N_ik + 2 K_ik`. -/

open Set MeasureTheory intervalIntegral Finset

namespace RHGammaExp0516
open RHLeg0503 RHSingDef0516 RHPairInt0516

/-! ### integrability combinators -/

lemma ii_mul_gt {f g : ℝ → ℝ} (h : IntervalIntegrable (fun u => f u * g u) volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => f u * (if c < u then g u else 0)) volume (-1) 1 := by
  have e : (fun u => f u * (if c < u then g u else 0)) = fun u => if c < u then f u * g u else 0 := by
    funext u; split_ifs <;> simp
  rw [e]; exact ii_gt h c

lemma ii_mul_le {f g : ℝ → ℝ} (h : IntervalIntegrable (fun u => f u * g u) volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => f u * (if u ≤ c then g u else 0)) volume (-1) 1 := by
  have e : (fun u => f u * (if u ≤ c then g u else 0)) = fun u => if u ≤ c then f u * g u else 0 := by
    funext u; split_ifs <;> simp
  rw [e]; exact ii_le h c

lemma ii_gt_mul {f g : ℝ → ℝ} (h : IntervalIntegrable (fun u => f u * g u) volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => (if c < u then f u else 0) * g u) volume (-1) 1 := by
  have e : (fun u => (if c < u then f u else 0) * g u) = fun u => if c < u then f u * g u else 0 := by
    funext u; split_ifs <;> simp
  rw [e]; exact ii_gt h c

lemma ii_le_mul {f g : ℝ → ℝ} (h : IntervalIntegrable (fun u => f u * g u) volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => (if u ≤ c then f u else 0) * g u) volume (-1) 1 := by
  have e : (fun u => (if u ≤ c then f u else 0) * g u) = fun u => if u ≤ c then f u * g u else 0 := by
    funext u; split_ifs <;> simp
  rw [e]; exact ii_le h c

lemma cont_ii {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume (-1) 1 := hf.intervalIntegrable _ _

lemma pm_def (n : ℕ) (s : ℝ) : pm n s = fun u => if s - 1 < u then p n (u - s) else 0 := rfl
lemma pp_def (n : ℕ) (s : ℝ) : pp n s = fun u => if u ≤ 1 - s then p n (u + s) else 0 := rfl

lemma cps (n : ℕ) (s : ℝ) : Continuous fun u => p n (u - s) := (continuous_p n).comp (continuous_id.sub continuous_const)
lemma cpa (n : ℕ) (s : ℝ) : Continuous fun u => p n (u + s) := (continuous_p n).comp (continuous_id.add continuous_const)

/-- `(pm_i + pp_i)(pm_k + pp_k)` pieces are integrable. -/
lemma ii_pieces (i k : ℕ) (s t : ℝ) :
    IntervalIntegrable (fun u => pm i s u * pm k t u) volume (-1) 1 ∧
    IntervalIntegrable (fun u => pm i s u * pp k t u) volume (-1) 1 ∧
    IntervalIntegrable (fun u => pp i s u * pm k t u) volume (-1) 1 ∧
    IntervalIntegrable (fun u => pp i s u * pp k t u) volume (-1) 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pm_def]; exact ii_gt_mul (ii_mul_gt (cont_ii ((cps i s).mul (cps k t))) _) _
  · simp only [pm_def, pp_def]; exact ii_gt_mul (ii_mul_le (cont_ii ((cps i s).mul (cpa k t))) _) _
  · simp only [pm_def, pp_def]; exact ii_le_mul (ii_mul_gt (cont_ii ((cpa i s).mul (cps k t))) _) _
  · simp only [pp_def]; exact ii_le_mul (ii_mul_le (cont_ii ((cpa i s).mul (cpa k t))) _) _

lemma lgp_ii (i : ℕ) (g : ℝ → ℝ) (hg : Continuous g) :
    IntervalIntegrable (fun u => lg u * p i u * g u) volume (-1) 1 := by
  have := lg_ii.mul_continuousOn ((continuous_p i).mul hg).continuousOn
  refine this.congr (fun u _ => ?_); simp only [Pi.mul_apply]; ring

lemma ii_lg_pieces (i k : ℕ) (s : ℝ) :
    IntervalIntegrable (fun u => lg u * p i u * pm k s u) volume (-1) 1 ∧
    IntervalIntegrable (fun u => lg u * p i u * pp k s u) volume (-1) 1 := by
  constructor
  · simp only [pm_def]; exact ii_mul_gt (lgp_ii i _ (cps k s)) _
  · simp only [pp_def]; exact ii_mul_le (lgp_ii i _ (cpa k s)) _

/-! ### the shifts as a `Fin 3` family -/

noncomputable def W (a : Fin 3) : ℝ := ![RHPrSum0511.w2, RHPrSum0511.w3, RHPrSum0511.w4] a
noncomputable def Sh (a : Fin 3) : ℝ := ![σ 2, σ 3, σ 4] a

lemma pr_sum (n : ℕ) (u : ℝ) : pr n u = ∑ a : Fin 3, W a * (pm n (Sh a) u + pp n (Sh a) u) := by
  simp [pr, W, Sh, Fin.sum_univ_three]

lemma ii_pr_pr (i k : ℕ) (a b : Fin 3) :
    IntervalIntegrable (fun u => W a * (pm i (Sh a) u + pp i (Sh a) u) * (W b * (pm k (Sh b) u + pp k (Sh b) u)))
      volume (-1) 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := ii_pieces i k (Sh a) (Sh b)
  have := (((h1.add h2).add h3).add h4).const_mul (W a * W b)
  refine this.congr (fun u _ => ?_); ring

/-- The prime–prime block. -/
theorem prpr (i k : ℕ) :
    ∫ u in (-1:ℝ)..1, pr i u * pr k u =
      ∑ a : Fin 3, ∑ b : Fin 3, W a * W b *
        ((∫ u in (-1:ℝ)..1, pm i (Sh a) u * pm k (Sh b) u) + (∫ u in (-1:ℝ)..1, pm i (Sh a) u * pp k (Sh b) u) +
         (∫ u in (-1:ℝ)..1, pp i (Sh a) u * pm k (Sh b) u) + (∫ u in (-1:ℝ)..1, pp i (Sh a) u * pp k (Sh b) u)) := by
  have e : (fun u => pr i u * pr k u) = fun u => ∑ a : Fin 3, ∑ b : Fin 3,
      W a * (pm i (Sh a) u + pp i (Sh a) u) * (W b * (pm k (Sh b) u + pp k (Sh b) u)) := by
    funext u; rw [pr_sum, pr_sum, sum_mul_sum]
  rw [e, intervalIntegral.integral_finsetSum (fun a _ => ?_)]
  · refine sum_congr rfl (fun a _ => ?_)
    rw [intervalIntegral.integral_finsetSum (fun b _ => ii_pr_pr i k a b)]
    refine sum_congr rfl (fun b _ => ?_)
    obtain ⟨h1, h2, h3, h4⟩ := ii_pieces i k (Sh a) (Sh b)
    rw [← intervalIntegral.integral_add h1 h2, ← intervalIntegral.integral_add (h1.add h2) h3,
      ← intervalIntegral.integral_add ((h1.add h2).add h3) h4, ← intervalIntegral.integral_const_mul]
    congr 1; funext u; ring
  · exact (IntervalIntegrable.sum (Finset.univ) (fun b _ => ii_pr_pr i k a b)).congr
      (fun u _ => by simp [Finset.sum_apply])

end RHGammaExp0516

