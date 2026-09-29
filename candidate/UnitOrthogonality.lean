import ExpectedRodrigues
import PolynomialIBP
open Polynomial MeasureTheory
namespace RHLegendreContract

theorem Q_integral_mul_eq_zero_of_degree (n : ℕ) (P : Polynomial ℝ)
    (hp : P.natDegree < n) :
    (∫ x in (0:ℝ)..1, (Q n).eval x * P.eval x) = 0 := by
  have h := RHPolynomialIBP.integral_iterate_derivative_mul n (rod n) P
    (fun k hk => ⟨rod_endpoint_zero n k hk, rod_endpoint_one n k hk⟩)
  rw [Polynomial.iterate_derivative_eq_zero hp] at h
  simp only [Polynomial.eval_zero, mul_zero, intervalIntegral.integral_zero, mul_zero] at h
  have hf : (∫ x in (0:ℝ)..1, (derivative^[n] (rod n)).eval x * P.eval x) =
      (n.factorial:ℝ) * (∫ x in (0:ℝ)..1, (Q n).eval x * P.eval x) := by
    simp only [← rodrigues_real, Polynomial.eval_mul, Polynomial.eval_natCast, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  rw [hf] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

theorem Q_orthogonal (m n : ℕ) (hmn : m≠n) :
    (∫ x in (0:ℝ)..1, (Q m).eval x * (Q n).eval x) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · simpa only [mul_comm] using
      Q_integral_mul_eq_zero_of_degree n (Q m) ((Q_natDegree_le m).trans_lt h)
  · exact Q_integral_mul_eq_zero_of_degree m (Q n) ((Q_natDegree_le n).trans_lt h)
end RHLegendreContract
