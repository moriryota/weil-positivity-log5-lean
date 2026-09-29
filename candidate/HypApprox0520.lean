import CcSs0510
import Mathlib.Algebra.Polynomial.BigOperators

namespace RHHypApprox0520
open Finset Polynomial
open scoped BigOperators

noncomputable def hypPoly (odd : Bool) : Polynomial ℝ :=
  ∑ m ∈ range 30, C (if m % 2 = (if odd then 1 else 0) then 1 / ((2:ℝ)^m * m.factorial) else 0) * X^m

lemma hypPoly_eval (odd : Bool) (x : ℝ) : (hypPoly odd).eval x =
    ∑ m ∈ range 30, if m % 2 = (if odd then 1 else 0) then (x/2)^m / m.factorial else 0 := by
  simp only [hypPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  apply sum_congr rfl
  intro m _
  split_ifs <;> simp [div_pow] <;> ring

lemma hypPoly_degree (odd : Bool) : (hypPoly odd).natDegree ≤ 29 := by
  unfold hypPoly
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have h : m ≤ 29 := by simp at hm; omega
  exact (natDegree_C_mul_le _ _).trans (by simpa using h)

theorem hyp_error {x : ℝ} (hx : |x/2| ≤ (1/2:ℝ)) :
    |Real.cosh (x/2) - (hypPoly false).eval x| ≤ (1/10^40:ℝ) ∧
    |Real.sinh (x/2) - (hypPoly true).eval x| ≤ (1/10^40:ℝ) := by
  have h := RHCcSs0510.exp_pair_bound (x := x/2) (by linarith) 30 (by norm_num)
  have hp := pow_le_pow_left₀ (abs_nonneg (x/2)) hx 30
  have hc : 0 ≤ ((31:ℝ) / ((30:ℕ).factorial * 30)) := by positivity
  have hb : (1/2:ℝ)^30 * ((31:ℝ) / ((30:ℕ).factorial * 30)) ≤ (1/10^40:ℝ) := by norm_num
  have hmul := (mul_le_mul_of_nonneg_right hp hc).trans hb
  rw [hypPoly_eval, hypPoly_eval]
  simp only [Bool.false_eq_true, if_false, if_true]
  constructor
  · exact h.1.trans hmul
  · exact h.2.trans hmul
end RHHypApprox0520
