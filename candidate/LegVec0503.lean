import Leg0503
import Cauchy0503

/-! # 0503: Legendre coefficient vectors and the exact vector operations

`evV N c u = Σ_{l<N} c_l P_l(u)`. Proved (as functions of `u`):
* `Im (evV N c) = evV (N+1) (ImV N c)` (integration from −1),
* `x · evV N c = evV (N+1) (XV N c)` (three-term recurrence),
* `Ip^[m] f = (Im^[m] (f ∘ neg)) ∘ neg` and `P_n ∘ neg = (−1)^n P_n` (reflection).
 -/

open Finset intervalIntegral
open scoped BigOperators

namespace RHLegVec0503
open RHLeg0503 RHCauchy0503

noncomputable def evV (N : ℕ) (c : ℕ → ℝ) (u : ℝ) : ℝ := ∑ l ∈ range N, c l * p l u

lemma continuous_evV (N : ℕ) (c : ℕ → ℝ) : Continuous (evV N c) := by
  unfold evV
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_p l))

/-- Legendre coefficient `m` of `∫_{−1}^u P_l`. -/
noncomputable def eI : ℕ → ℕ → ℝ
  | 0, m => (if m = 0 then 1 else 0) + (if m = 1 then 1 else 0)
  | k + 1, m => (if m = k + 2 then 1 / (2 * (k : ℝ) + 3) else 0) - (if m = k then 1 / (2 * (k : ℝ) + 3) else 0)

lemma Im_p (l N : ℕ) (hN : l + 2 ≤ N) (u : ℝ) : Im (p l) u = ∑ m ∈ range N, eI l m * p m u := by
  cases l with
  | zero =>
      simp only [eI, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_range]
      rw [if_pos (by omega), if_pos (by omega)]
      exact integral_left_zero u
  | succ k =>
      simp only [eI, sub_mul, ite_mul, zero_mul, sum_sub_distrib, sum_ite_eq', mem_range]
      rw [if_pos (by omega), if_pos (by omega), Im, integral_left_succ k u]
      ring

lemma Im_linear (N : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    Im (evV N c) u = ∑ l ∈ range N, c l * Im (p l) u := by
  unfold Im evV
  have h := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := -1) (b := u)
    (s := range N) (f := fun l v => c l * p l v)
    (fun l _ => ((continuous_const.mul (continuous_p l)).intervalIntegrable _ _))
  rw [h]
  exact sum_congr rfl (fun l _ => integral_const_mul _ _)

noncomputable def ImV (N : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ := ∑ l ∈ range N, c l * eI l m

theorem Im_evV (N : ℕ) (c : ℕ → ℝ) : Im (evV N c) = evV (N + 1) (ImV N c) := by
  funext u
  rw [Im_linear]
  unfold evV ImV
  have h : ∀ l ∈ range N, c l * Im (p l) u = ∑ m ∈ range (N + 1), c l * eI l m * p m u := by
    intro l hl
    rw [Im_p l (N + 1) (by simp at hl; omega) u, mul_sum]
    exact sum_congr rfl (fun m _ => by ring)
  rw [sum_congr rfl h, sum_comm]
  exact sum_congr rfl (fun m _ => by rw [sum_mul])

/-- Legendre coefficient `m` of `x · P_l`. -/
noncomputable def eX : ℕ → ℕ → ℝ
  | 0, m => if m = 1 then 1 else 0
  | k + 1, m => (if m = k + 2 then ((k : ℝ) + 2) / (2 * k + 3) else 0) +
      (if m = k then ((k : ℝ) + 1) / (2 * k + 3) else 0)

lemma X_p (l N : ℕ) (hN : l + 2 ≤ N) (u : ℝ) : u * p l u = ∑ m ∈ range N, eX l m * p m u := by
  cases l with
  | zero =>
      simp only [eX, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
      rw [if_pos (by omega)]
      exact x_mul_zero u
  | succ k =>
      simp only [eX, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_range]
      rw [if_pos (by omega), if_pos (by omega), x_mul_succ k u]
      ring

noncomputable def XV (N : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ := ∑ l ∈ range N, c l * eX l m

theorem X_evV (N : ℕ) (c : ℕ → ℝ) (u : ℝ) : u * evV N c u = evV (N + 1) (XV N c) u := by
  unfold evV XV
  rw [mul_sum]
  have h : ∀ l ∈ range N, u * (c l * p l u) = ∑ m ∈ range (N + 1), c l * eX l m * p m u := by
    intro l hl
    rw [mul_left_comm, X_p l (N + 1) (by simp at hl; omega) u, mul_sum]
    exact sum_congr rfl (fun m _ => by ring)
  rw [sum_congr rfl h, sum_comm]
  exact sum_congr rfl (fun m _ => by rw [sum_mul])

/-! ## Reflection -/

lemma Ip_neg {f : ℝ → ℝ} (u : ℝ) : Ip f u = Im (fun w => f (-w)) (-u) := by
  unfold Ip Im
  rw [intervalIntegral.integral_comp_neg (fun w => f w)]
  simp

theorem Ip_iter : ∀ (m : ℕ) (f : ℝ → ℝ) (u : ℝ), (Ip^[m] f) u = (Im^[m] (fun w => f (-w))) (-u)
  | 0, f, u => by simp
  | m + 1, f, u => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Ip_iter m (Ip f) u]
      have e : (fun w => Ip f (-w)) = Im (fun w => f (-w)) := by
        funext w; rw [Ip_neg, neg_neg]
      rw [e]

lemma Im_smul (a : ℝ) (f : ℝ → ℝ) : Im (fun u => a * f u) = fun u => a * Im f u := by
  funext u; unfold Im; exact integral_const_mul _ _

theorem Im_iter_smul : ∀ (m : ℕ) (a : ℝ) (f : ℝ → ℝ),
    Im^[m] (fun u => a * f u) = fun u => a * (Im^[m] f) u
  | 0, a, f => rfl
  | m + 1, a, f => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Im_smul, Im_iter_smul m]

theorem Ip_iter_p (m n : ℕ) (u : ℝ) : (Ip^[m] (p n)) u = (-1) ^ n * (Im^[m] (p n)) (-u) := by
  rw [Ip_iter]
  have e : (fun w => p n (-w)) = fun w => (-1) ^ n * p n w := funext (fun w => p_neg n w)
  rw [e, Im_iter_smul]

lemma evV_neg (N : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    evV N c (-u) = evV N (fun l => (-1) ^ l * c l) u := by
  unfold evV
  exact sum_congr rfl (fun l _ => by rw [p_neg]; ring)

end RHLegVec0503

