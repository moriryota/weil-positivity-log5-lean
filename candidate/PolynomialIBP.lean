import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

open Polynomial MeasureTheory Set intervalIntegral

namespace RHPolynomialIBP

/-- One step of integration by parts on `[0,1]` for real polynomials, under the
assumption that the endpoint values `F(0) = F(1) = 0` vanish. -/
theorem integral_derivative_mul_eq_neg
    (F P : Polynomial ℝ) (hF0 : F.eval 0 = 0) (hF1 : F.eval 1 = 0) :
    ∫ x in (0:ℝ)..1, (derivative F).eval x * P.eval x
      = - ∫ x in (0:ℝ)..1, F.eval x * (derivative P).eval x := by
  have key := integral_mul_deriv_eq_deriv_mul
    (u := fun x => F.eval x) (u' := fun x => (derivative F).eval x)
    (v := fun x => P.eval x) (v' := fun x => (derivative P).eval x)
    (a := 0) (b := 1)
    (fun x _ => F.hasDerivAt x) (fun x _ => P.hasDerivAt x)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  rw [hF0, hF1] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  linarith [key]

/-- Iterated integration by parts on `[0,1]` for real polynomials.  If all
derivatives of `F` of order `< n` vanish at both endpoints `0` and `1`, then
`n` derivatives can be moved from `F` onto `P` at the cost of a sign `(-1)^n`. -/
theorem integral_iterate_derivative_mul :
    ∀ (n : ℕ) (F P : Polynomial ℝ),
      (∀ k < n, (derivative^[k] F).eval (0:ℝ) = 0 ∧ (derivative^[k] F).eval (1:ℝ) = 0) →
      ∫ x in (0:ℝ)..1, (derivative^[n] F).eval x * P.eval x
        = (-1:ℝ) ^ n * ∫ x in (0:ℝ)..1, F.eval x * (derivative^[n] P).eval x := by
  intro n
  induction n with
  | zero =>
    intro F P _
    simp
  | succ n ih =>
    intro F P hF
    have hIH := ih (derivative F) P (by
      intro k hk
      have hk1 := hF (k + 1) (by omega)
      simpa [Function.iterate_succ_apply] using hk1)
    have hbase := integral_derivative_mul_eq_neg F (derivative^[n] P)
      (hF 0 (by omega)).1 (hF 0 (by omega)).2
    rw [Function.iterate_succ_apply (f := derivative) (n := n) (x := F)]
    rw [hIH, hbase, ← Function.iterate_succ_apply' derivative n P]
    ring


end RHPolynomialIBP
