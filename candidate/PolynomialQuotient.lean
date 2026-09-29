import ComplexMonomial
open Polynomial MeasureTheory Set
open scoped BigOperators
namespace RHTuckPolynomial

noncomputable def quotient (p : Polynomial ℂ) (x y : ℝ) : ℂ :=
  (p.eval (x:ℂ)-p.eval (y:ℂ))/((|x-y|:ℝ):ℂ)

lemma quotient_eq_sum (p : Polynomial ℂ) (x y : ℝ) :
    quotient p x y = ∑ n ∈ p.support,
      p.coeff n * (((x:ℂ)^n-(y:ℂ)^n)/((|x-y|:ℝ):ℂ)) := by
  unfold quotient
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma quotient_integrable (p : Polynomial ℂ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    IntervalIntegrable (quotient p x) volume (-1) 1 := by
  have h : quotient p x = fun y : ℝ => ∑ n ∈ p.support,
      p.coeff n * (((x:ℂ)^n-(y:ℂ)^n)/((|x-y|:ℝ):ℂ)) := funext (quotient_eq_sum p x)
  rw [h]
  constructor
  · exact integrable_finsetSum p.support (fun n hn =>
      ((RHTuckComplex.complex_integrable n hx).const_mul (p.coeff n)).1)
  · exact integrable_finsetSum p.support (fun n hn =>
      ((RHTuckComplex.complex_integrable n hx).const_mul (p.coeff n)).2)

theorem integral_eq_sum (p : Polynomial ℂ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    (∫ y in (-1:ℝ)..1, quotient p x y) = ∑ n ∈ p.support,
      p.coeff n * (RHTuckMonomial.image n).eval (x:ℂ) := by
  simp only [quotient_eq_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun n hn => (RHTuckComplex.complex_integrable n hx).const_mul _)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul,RHTuckComplex.complex_integral n hx]
end RHTuckPolynomial
