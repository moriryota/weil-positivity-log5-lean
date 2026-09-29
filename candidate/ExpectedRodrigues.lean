import RodriguesEndpoints
open Polynomial
namespace RHLegendreContract

theorem Q_natDegree_le (n : ℕ) : (Q n).natDegree ≤ n := by
  exact (Polynomial.natDegree_map_le).trans_eq (Polynomial.natDegree_shiftedLegendre n)

theorem Q_higher_derivative_zero (m n : ℕ) (h : m<n) :
    derivative^[n] (Q m) = 0 :=
  Polynomial.iterate_derivative_eq_zero ((Q_natDegree_le m).trans_lt h)
end RHLegendreContract
namespace RHExpected0243

theorem endpoints (n k : ℕ) (hk : k<n) :
    (derivative^[k] ((X:Polynomial ℝ)^n * (1-X)^n)).eval 0 = 0 ∧
    (derivative^[k] ((X:Polynomial ℝ)^n * (1-X)^n)).eval 1 = 0 :=
  ⟨RHLegendreContract.rod_endpoint_zero n k hk,
   RHLegendreContract.rod_endpoint_one n k hk⟩

theorem rodrigues_eval (n : ℕ) (x : ℝ) :
    (derivative^[n] ((X:Polynomial ℝ)^n*(1-X)^n)).eval x =
      (n.factorial:ℝ) * (RHLegendreContract.Q n).eval x := by
  have h := congrArg (Polynomial.eval x) (RHLegendreContract.rodrigues_real n)
  simpa [RHLegendreContract.rod] using h.symm
end RHExpected0243
