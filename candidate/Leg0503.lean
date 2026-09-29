import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # 0503: Legendre polynomials on [-1,1] and the identities used by the Legendre-basis algorithm

`leg n` by the three-term recurrence. Proved in general (pointwise, joint induction), with
`p n x = (leg n).eval x`, `d n x = (derivative (leg n)).eval x`:
* `x d(n+1) − d n = (n+1) p(n+1)` and `(x²−1) d(n+1) = (n+1)(x p(n+1) − p n)`;
* `d(n+2) = x d(n+1) + (n+2) p(n+1)`, `d(n+2) − d n = (2n+3) p(n+1)`;
* `p n 1 = 1`, `p n (−1) = (−1)^n`, `p n (−x) = (−1)^n p n x`;
* `∫_{−1}^u p(n+1) = (p(n+2) u − p n u)/(2n+3)`, `∫_{−1}^u p 0 = p 0 u + p 1 u`,
  `∫_u^1 p(n+1) = −(p(n+2) u − p n u)/(2n+3)`, `∫_u^1 p 0 = p 0 u − p 1 u`. -/

open Polynomial

namespace RHLeg0503

noncomputable def leg : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => X
  | n + 2 => C (1 / ((n : ℝ) + 2)) * (C (2 * (n : ℝ) + 3) * X * leg (n + 1) - C ((n : ℝ) + 1) * leg n)

noncomputable def p (n : ℕ) (x : ℝ) : ℝ := (leg n).eval x
noncomputable def d (n : ℕ) (x : ℝ) : ℝ := (derivative (leg n)).eval x

lemma p_zero (x : ℝ) : p 0 x = 1 := by simp [p, leg]
lemma p_one (x : ℝ) : p 1 x = x := by simp [p, leg]
lemma d_zero (x : ℝ) : d 0 x = 0 := by simp [d, leg]
lemma d_one (x : ℝ) : d 1 x = 1 := by simp [d, leg]

lemma p_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * p (n + 2) x = (2 * n + 3) * x * p (n + 1) x - (n + 1) * p n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [p, leg, eval_mul, eval_C, eval_sub, eval_X]
  field_simp

lemma d_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * d (n + 2) x = (2 * n + 3) * (p (n + 1) x + x * d (n + 1) x) - (n + 1) * d n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [d, p, leg, derivative_mul, derivative_C, derivative_X, derivative_sub, eval_mul, eval_C,
    eval_sub, eval_X, eval_add, zero_mul, zero_add, mul_one]
  field_simp

theorem legS (x : ℝ) : ∀ n : ℕ,
    x * d (n + 1) x - d n x = (n + 1) * p (n + 1) x ∧
    (x ^ 2 - 1) * d (n + 1) x = (n + 1) * (x * p (n + 1) x - p n x)
  | 0 => by simp [p_zero, p_one, d_zero, d_one]; ring
  | n + 1 => by
      obtain ⟨s1, s2⟩ := legS x n
      have hr := p_rec n x
      have drec := d_rec n x
      have key : ((n : ℝ) + 2) * (d (n + 2) x - (x * d (n + 1) x + (n + 2) * p (n + 1) x)) = 0 := by
        linear_combination drec + (n + 1) * s1
      have hi : d (n + 2) x = x * d (n + 1) x + (n + 2) * p (n + 1) x := by
        have := (mul_eq_zero.mp key).resolve_left (by positivity)
        linarith
      push_cast
      constructor
      · linear_combination x * hi + s2 - hr
      · linear_combination (x ^ 2 - 1) * hi + x * s2 - x * hr

lemma d_step (n : ℕ) (x : ℝ) : d (n + 2) x = x * d (n + 1) x + (n + 2) * p (n + 1) x := by
  obtain ⟨s1, s2⟩ := legS x (n + 1)
  obtain ⟨t1, t2⟩ := legS x n
  have drec := d_rec n x
  have key : ((n : ℝ) + 2) * (d (n + 2) x - (x * d (n + 1) x + (n + 2) * p (n + 1) x)) = 0 := by
    linear_combination drec + (n + 1) * t1
  have := (mul_eq_zero.mp key).resolve_left (by positivity)
  linarith

/-- `P'_{n+2} − P'_n = (2n+3) P_{n+1}`. -/
lemma d_diff (n : ℕ) (x : ℝ) : d (n + 2) x - d n x = (2 * n + 3) * p (n + 1) x := by
  have h := d_step n x
  have t1 := (legS x n).1
  linear_combination h + t1

lemma p_at_one : ∀ n : ℕ, p n 1 = 1
  | 0 => p_zero 1
  | 1 => p_one 1
  | n + 2 => by
      have h := p_rec n 1
      rw [p_at_one (n + 1), p_at_one n] at h
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      rw [h]; ring

lemma p_neg : ∀ (n : ℕ) (x : ℝ), p n (-x) = (-1) ^ n * p n x
  | 0, x => by simp [p_zero]
  | 1, x => by simp [p_one]
  | n + 2, x => by
      have h1 := p_rec n (-x)
      have h2 := p_rec n x
      rw [p_neg (n + 1) x, p_neg n x] at h1
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      rw [h1]
      linear_combination (-(-1) ^ n) * h2

lemma p_at_neg_one (n : ℕ) : p n (-1) = (-1) ^ n := by
  rw [p_neg, p_at_one, mul_one]

lemma hasDerivAt_p (n : ℕ) (x : ℝ) : HasDerivAt (p n) (d n x) x := (leg n).hasDerivAt x

lemma continuous_p (n : ℕ) : Continuous (p n) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_p n x).continuousAt)

/-- `∫_{−1}^u P_{n+1} = (P_{n+2}(u) − P_n(u))/(2n+3)`. -/
theorem integral_left_succ (n : ℕ) (u : ℝ) :
    ∫ v in (-1:ℝ)..u, p (n + 1) v = (p (n + 2) u - p n u) / (2 * n + 3) := by
  have hc : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => (p (n + 2) v - p n v) / (2 * n + 3))
    (fun v _ => by
      have h := ((hasDerivAt_p (n + 2) v).sub (hasDerivAt_p n v)).div_const (2 * (n : ℝ) + 3)
      rw [d_diff n v] at h
      convert h using 1; field_simp)
    ((continuous_p _).intervalIntegrable _ _)]
  rw [p_at_neg_one, p_at_neg_one, pow_succ, pow_succ]; ring

theorem integral_left_zero (u : ℝ) : ∫ v in (-1:ℝ)..u, p 0 v = p 0 u + p 1 u := by
  simp only [p_zero, p_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]; (try ring)

theorem integral_right_succ (n : ℕ) (u : ℝ) :
    ∫ v in u..(1:ℝ), p (n + 1) v = -((p (n + 2) u - p n u) / (2 * n + 3)) := by
  have hc : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => (p (n + 2) v - p n v) / (2 * n + 3))
    (fun v _ => by
      have h := ((hasDerivAt_p (n + 2) v).sub (hasDerivAt_p n v)).div_const (2 * (n : ℝ) + 3)
      rw [d_diff n v] at h
      convert h using 1; field_simp)
    ((continuous_p _).intervalIntegrable _ _)]
  rw [p_at_one, p_at_one]; ring

theorem integral_right_zero (u : ℝ) : ∫ v in u..(1:ℝ), p 0 v = p 0 u - p 1 u := by
  simp only [p_zero, p_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]; (try ring)

/-- Multiplication by `x`: `x P_{n+1} = ((n+2) P_{n+2} + (n+1) P_n)/(2n+3)`. -/
theorem x_mul_succ (n : ℕ) (x : ℝ) :
    x * p (n + 1) x = (((n : ℝ) + 2) * p (n + 2) x + (n + 1) * p n x) / (2 * n + 3) := by
  have hc : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  rw [p_rec n x]; field_simp; ring

theorem x_mul_zero (x : ℝ) : x * p 0 x = p 1 x := by simp [p_zero, p_one]

end RHLeg0503

