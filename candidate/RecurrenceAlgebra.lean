import Mathlib.Tactic
namespace RHRecurrenceAlgebra
/-- Algebraic certificate for an interior coefficient; concrete coefficient
identities and boundary cases are separate hypotheses. -/
theorem interior_certificate (n k A B C D : ℝ)
    (ha : n+1-k ≠ 0) (hd : n+k+2 ≠ 0)
    (h1 : (n+1-k)*A=(n+k+3)*B)
    (h2 : (n-k)*B=(n+k+2)*C)
    (h3 : (k+1)^2*B=(n+1-k)*(n+k+2)*D) :
    (n+2)*A-(2*n+3)*B-2*(2*n+3)*D+(n+1)*C=0 := by
  have h : ((n+1-k)*(n+k+2))*
      ((n+2)*A-(2*n+3)*B-2*(2*n+3)*D+(n+1)*C)=0 := by
    linear_combination (n+2)*(n+k+2)*h1 - (n+1)*(n+1-k)*h2 + 2*(2*n+3)*h3
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero ha hd)
end RHRecurrenceAlgebra
