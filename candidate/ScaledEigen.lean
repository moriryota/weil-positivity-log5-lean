import DirectionScaling
import IntegralScaling
import UnitEigen
open Polynomial MeasureTheory Set
namespace RHTuckScaledEigen
open RHLegendreDirections RHDirectionScaling

theorem integral_eigen {L : ℝ} (hL : 0 < L) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-L) L) :
    (∫ y in (-L)..L,
      ((directionPoly L n).eval (x:ℂ)-(directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)) =
      (2*(harmonic n:ℂ)) * (directionPoly L n).eval (x:ℂ) := by
  have hu : x/L ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hL).mpr
      linarith [hx.1]
    · apply (div_le_iff₀ hL).mpr
      linarith [hx.2]
  have ht := RHTuckScaling.integral_scale
    (fun t : ℝ => (directionPoly 1 n).eval (t:ℂ)) (factor L n) hL (x/L)
  have hxu : L*(x/L) = x := by field_simp
  rw [hxu] at ht
  simp_rw [direction_eval_scale hL n]
  rw [ht,RHTuckUnitEigen.integral_eigen n hu]
  ring
end RHTuckScaledEigen
