import ScaledIntegrable
open Polynomial MeasureTheory Set
namespace RHExpected0276

theorem actual_scaled_direction {L : ℝ} (hL : 0 < L) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-L) L) :
    IntervalIntegrable (fun y : ℝ =>
      ((RHLegendreDirections.directionPoly L n).eval (x:ℂ)-
       (RHLegendreDirections.directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)) volume (-L) L ∧
    (∫ y in (-L)..L,
      ((RHLegendreDirections.directionPoly L n).eval (x:ℂ)-
       (RHLegendreDirections.directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)) =
      (2*(harmonic n:ℂ)) * (RHLegendreDirections.directionPoly L n).eval (x:ℂ) :=
  ⟨RHTuckScaledEigen.quotient_integrable hL n hx,RHTuckScaledEigen.integral_eigen hL n hx⟩
end RHExpected0276
