import Prod0508
import LogMoment0508
import Link0505

/-! # 0508: integrals of Legendre vectors against `log(1+u)` and `(1+u)^m`

* `∫_{−1}^1 log(1+u) evV N c = Σ_{l<N} c_l μ_l`,
* `∫_{−1}^1 (1+u)^m evV N c = Σ_{l<N} c_l · 2/(2l+1) · β 0 m l`,
* reflection: `∫_{−1}^1 f(1−u) g(u) du = ∫_{−1}^1 f(1+u) g(−u) du`. -/

open Finset intervalIntegral
open scoped BigOperators

namespace RHTpA0508
open RHLeg0503 RHLegVec0503 RHIter0505 RHLogMoment0508

noncomputable def muR : ℕ → ℝ
  | 0 => 2 * Real.log 2 - 2
  | m + 1 => 2 * (-1) ^ (m + 2) / ((m + 1) * (m + 2))

lemma mu_eq (l : ℕ) : ∫ x in (-1:ℝ)..1, Real.log (1 + x) * p l x = muR l := by
  cases l with
  | zero => rw [mu_zero]; rfl
  | succ m => rw [mu_succ]; simp [muR]

theorem logint (N : ℕ) (c : ℕ → ℝ) :
    ∫ u in (-1:ℝ)..1, Real.log (1 + u) * evV N c u = ∑ l ∈ range N, c l * muR l := by
  unfold evV
  have e : (fun u => Real.log (1 + u) * ∑ l ∈ range N, c l * p l u) =
      fun u => ∑ l ∈ range N, c l * (Real.log (1 + u) * p l u) := by
    funext u; rw [mul_sum]; exact sum_congr rfl (fun l _ => by ring)
  rw [e, integral_finsetSum (fun l _ => (log1p_ii.mul_continuousOn (continuous_p l).continuousOn).const_mul _)]
  exact sum_congr rfl (fun l _ => by rw [integral_const_mul, mu_eq])

theorem powint (m N : ℕ) (c : ℕ → ℝ) :
    ∫ u in (-1:ℝ)..1, (1 + u) ^ m * evV N c u = ∑ l ∈ range N, c l * (2 / (2 * l + 1) * β 0 m l) := by
  have hb : ∀ u, (1 + u) ^ m = evV (0 + 1 + m) (β 0 m) u := by
    intro u; rw [← onePlus_p 0 m u, p_zero, mul_one]
  unfold evV at hb ⊢
  have e : (fun u => (1 + u) ^ m * ∑ l ∈ range N, c l * p l u) =
      fun u => ∑ l ∈ range N, ∑ i ∈ range (0 + 1 + m), c l * β 0 m i * (p i u * p l u) := by
    funext u; rw [hb u, sum_mul_sum, sum_comm]
    exact sum_congr rfl (fun l _ => sum_congr rfl (fun i _ => by ring))
  rw [e, integral_finsetSum (f := fun l u => ∑ i ∈ range (0 + 1 + m), c l * β 0 m i * (p i u * p l u))
    (fun l _ => (continuous_finsetSum _ (fun i _ =>
    (continuous_const.mul ((continuous_p i).mul (continuous_p l))))).intervalIntegrable _ _)]
  refine sum_congr rfl (fun l _ => ?_)
  rw [integral_finsetSum (f := fun i u => c l * β 0 m i * (p i u * p l u))
    (fun i _ => ((continuous_const.mul ((continuous_p i).mul (continuous_p l)))).intervalIntegrable _ _)]
  simp_rw [integral_const_mul, RHLink0505.orth]
  by_cases hl : l < 0 + 1 + m
  · rw [sum_eq_single l (fun i _ hi => by rw [if_neg hi, mul_zero]) (fun h => absurd (mem_range.mpr hl) h), if_pos rfl]
    ring
  · rw [β_supp 0 m l (by omega), sum_eq_zero (fun i hi => by simp at hi; rw [if_neg (by omega), mul_zero])]
    ring

theorem refl_int {f g : ℝ → ℝ} :
    ∫ u in (-1:ℝ)..1, f (1 - u) * g u = ∫ u in (-1:ℝ)..1, f (1 + u) * g (-u) := by
  have h := intervalIntegral.integral_comp_neg (a := -1) (b := 1) (fun u => f (1 + u) * g (-u))
  simp only [neg_neg] at h
  rw [← h]
  congr 1

end RHTpA0508

