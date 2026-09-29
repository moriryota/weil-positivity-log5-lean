import LegendreContract
import RecurrenceBasis

open Polynomial MeasureTheory Set
namespace RHLegendreContract

/-- Conditional interface to the numerical recurrence. The three polynomial
identities supplied here must be discharged by ShiftedRecurrence. -/
theorem recPoly_eval_eq_Q_of_recurrence
    (h0 : Q 0 = 1) (h1 : Q 1 = 1-Polynomial.C 2*Polynomial.X)
    (hr : ∀ n : ℕ, Polynomial.C ((n:ℝ)+2)*Q (n+2) =
      Polynomial.C (2*(n:ℝ)+3)*(1-Polynomial.C 2*Polynomial.X)*Q (n+1) -
        Polynomial.C ((n:ℝ)+1)*Q n)
    {L : ℝ} (hL : 0 < L) (n : ℕ) (x : ℝ) :
    (RHLegendreDirections.recPoly L n).eval (x:ℂ) =
      (((Q n).eval (1/2-x/(2*L) : ℝ) : ℝ) : ℂ) := by
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  induction n using Nat.twoStepInduction with
  | zero => simp [RHLegendreDirections.recPoly_zero, h0]
  | one =>
    rw [RHLegendreDirections.recPoly_one, h1]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    field_simp [hLc]
    ring
  | more n ih0 ih1 =>
    have hq := congrArg (fun p : Polynomial ℝ => ((p.eval (1/2-x/(2*L) : ℝ) : ℝ) : ℂ)) (hr n)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X] at hq
    push_cast at hq
    have ht : (1:ℂ)-2*((1/2-x/(2*L):ℝ):ℂ) = (x:ℂ)/(L:ℂ) := by
      push_cast
      field_simp [hLc]
      ring
    have htc : (1:ℂ)-2*((1:ℂ)/2-(x:ℂ)/(2*(L:ℂ))) = (x:ℂ)/(L:ℂ) := by
      field_simp [hLc]
      ring
    rw [htc] at hq
    rw [RHLegendreDirections.recPoly_eval_step, ih0, ih1]
    have hn : (n:ℂ)+2 ≠ 0 := by
      exact_mod_cast (show (n:ℝ)+2 ≠ 0 by positivity)
    apply (mul_right_cancel₀ hn)
    have hcancel : (1/((n:ℂ)+2))*((n:ℂ)+2) = 1 := by field_simp
    rw [mul_assoc, hcancel, mul_one]
    linear_combination -hq

end RHLegendreContract
