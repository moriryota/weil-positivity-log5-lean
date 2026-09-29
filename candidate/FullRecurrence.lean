import CoefficientBoundary
open Polynomial
namespace RHLegendreContract

theorem Q_coeff_b (n k : ℕ) : (Q n).coeff k = (-1:ℝ)^k * (b n k:ℝ) := by
  rw [Q_coeff]
  simp only [b, Nat.cast_mul]
  ring

theorem Q_recurrence (n : ℕ) :
    Polynomial.C ((n:ℝ)+2)*Q (n+2) =
      Polynomial.C (2*(n:ℝ)+3)*(1-Polynomial.C 2*Polynomial.X)*Q (n+1) -
        Polynomial.C ((n:ℝ)+1)*Q n := by
  ext k
  simp only [mul_assoc, sub_mul, one_mul, coeff_sub, coeff_C_mul]
  cases k with
  | zero =>
    simp only [coeff_X_mul_zero, Q_coeff, pow_zero, Nat.choose_zero_right,
      Nat.add_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_zero, sub_zero]
    ring
  | succ k =>
    rw [coeff_X_mul]
    simp only [Q_coeff_b, pow_succ]
    have h := b_recurrence_succ n k
    linear_combination -((-1:ℝ)^k)*h
end RHLegendreContract
