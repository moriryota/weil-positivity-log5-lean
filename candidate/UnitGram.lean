import UnitOrthogonality
import TopDerivative
import BetaMoment
open Polynomial MeasureTheory
namespace RHLegendreContract

theorem Q_norm_sq (n : ℕ) :
    (∫ x in (0:ℝ)..1, (Q n).eval x * (Q n).eval x) = 1/(2*(n:ℝ)+1) := by
  have h := RHPolynomialIBP.integral_iterate_derivative_mul n (rod n) (Q n)
    (fun k hk => ⟨rod_endpoint_zero n k hk, rod_endpoint_one n k hk⟩)
  rw [← rodrigues_real, Q_top_derivative] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_C, mul_assoc,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const] at h
  have hs : (-1:ℝ)^n * (-1:ℝ)^n=1 := by rw [← mul_pow]; norm_num
  have hr : (-1:ℝ)^n * ((∫ x in (0:ℝ)..1, (rod n).eval x) *
      ((n.factorial:ℝ)*((-1:ℝ)^n*((n+n).choose n:ℝ)))) =
      (n.factorial:ℝ) * (((n+n).choose n:ℝ)*(∫ x in (0:ℝ)..1, (rod n).eval x)) := by
    calc
      _ = ((-1:ℝ)^n * (-1:ℝ)^n) * ((n.factorial:ℝ) *
          (((n+n).choose n:ℝ)*(∫ x in (0:ℝ)..1, (rod n).eval x))) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [hr] at h
  have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi := (mul_left_cancel₀ hf) h
  rw [hi]
  simp only [rod, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  rw [beta_moment]
  have hc : ((n+n).choose n:ℝ) * (n.factorial:ℝ) * n.factorial = (n+n).factorial := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
  rw [← mul_div_assoc, ← mul_assoc, hc, Nat.factorial_succ]
  push_cast
  have hn : ((n+n).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+n)
  field_simp
  <;> ring

theorem Q_unit_gram (m n : ℕ) :
    (∫ x in (0:ℝ)..1, (Q m).eval x*(Q n).eval x) =
      if m=n then 1/(2*(n:ℝ)+1) else 0 := by
  by_cases h : m=n
  · subst m
    simpa using Q_norm_sq n
  · simpa [h] using Q_orthogonal m n h
end RHLegendreContract
