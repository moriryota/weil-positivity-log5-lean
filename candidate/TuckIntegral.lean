import TuckMonomial
import SingularMonomial
open Polynomial Set
open scoped BigOperators
namespace RHTuckIntegral

lemma eval_image (n : ℕ) (x : ℝ) :
    (RHTuckMonomial.image n).eval (x : ℂ) = (RHDividedMoments.action n x : ℂ) := by
  rw [RHDividedMoments.action_formula]
  simp only [RHTuckMonomial.image, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  push_cast
  rfl

/-- The algebraic monomial image is the genuine singular integral on the unit interval. -/
theorem monomial_integral (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (((∫ y in (-1 : ℝ)..1, (x^n-y^n)/|x-y|) : ℝ) : ℂ) =
      (RHTuckMonomial.image n).eval (x : ℂ) := by
  rw [RHDividedMoments.singular_eq_action n hx, eval_image]
end RHTuckIntegral
