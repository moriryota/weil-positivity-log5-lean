import TuckLinear
import PolynomialQuotient
open Polynomial MeasureTheory Set
open scoped BigOperators
namespace RHTuckPolynomial

theorem integral_eq_operator (p : Polynomial ℂ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    (∫ y in (-1:ℝ)..1, quotient p x y) = (RHTuckLinear.operator p).eval (x:ℂ) := by
  rw [integral_eq_sum p hx,RHTuckLinear.operator_eq_sum]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul]
end RHTuckPolynomial
