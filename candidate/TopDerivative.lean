import ExpectedRodrigues
import ShiftedCoefficient
open Polynomial
namespace RHLegendreContract

theorem derivative_top_of_degree_le (P : Polynomial ℝ) (n : ℕ) (hn : P.natDegree ≤ n) :
    derivative^[n] P = C ((n.factorial:ℝ)*P.coeff n) := by
  ext k
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hk : k=0
  · subst k
    simp [Nat.descFactorial_self, nsmul_eq_mul]
  · rw [Polynomial.coeff_C, if_neg hk]
    have hcoeff : P.coeff (k+n)=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff, smul_zero]

theorem Q_top_derivative (n : ℕ) : derivative^[n] (Q n) =
    C ((n.factorial:ℝ)*((-1:ℝ)^n*((n+n).choose n:ℝ))) := by
  rw [derivative_top_of_degree_le (Q n) n (Q_natDegree_le n), Q_coeff]
  simp
end RHLegendreContract
