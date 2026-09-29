import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic
open MeasureTheory
namespace RHLegendreContract

theorem beta_moment (m n : ℕ) :
    (∫ x in (0:ℝ)..1, x^m*(1-x)^n) =
      (m.factorial:ℝ)*n.factorial/(m+n+1).factorial := by
  have hm : 0 < ((m:ℂ)+1).re := by simp; positivity
  have hn : 0 < ((n:ℂ)+1).re := by simp; positivity
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m:ℂ)+1) ((n:ℂ)+1) hm hn
  have hs : (m:ℂ)+1+((n:ℂ)+1) = ((m+n+1:ℕ):ℂ)+1 := by push_cast; ring
  rw [hs, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  simp only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast] at h
  have hc : (∫ x in (0:ℝ)..1, (x:ℂ)^m*(1-(x:ℂ))^n) =
      ((∫ x in (0:ℝ)..1, x^m*(1-x)^n : ℝ):ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext x
    push_cast
    rfl
  rw [hc] at h
  have hr := congrArg Complex.re h
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re] using hr
end RHLegendreContract
