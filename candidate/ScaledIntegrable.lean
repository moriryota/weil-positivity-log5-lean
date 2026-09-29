import ScaledEigen
open Polynomial MeasureTheory Set
namespace RHTuckScaledEigen
open RHLegendreDirections RHDirectionScaling

theorem quotient_integrable {L : ℝ} (hL : 0 < L) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-L) L) :
    IntervalIntegrable (fun y : ℝ =>
      ((directionPoly L n).eval (x:ℂ)-(directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ))
      volume (-L) L := by
  have hu : x/L ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hL).mpr
      linarith [hx.1]
    · apply (div_le_iff₀ hL).mpr
      linarith [hx.2]
  let g : ℝ → ℂ := fun y =>
    ((directionPoly L n).eval (x:ℂ)-(directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)
  have he : (fun t => g (L*t)) = fun t =>
      ((L:ℂ)⁻¹ * factor L n) * RHTuckPolynomial.quotient (directionPoly 1 n) (x/L) t := by
    funext t
    have ht := RHTuckScaling.quotient_scale
      (fun u : ℝ => (directionPoly 1 n).eval (u:ℂ)) (factor L n) hL (x/L) t
    have hxu : L*(x/L) = x := by field_simp
    rw [hxu] at ht
    dsimp [g]
    simp_rw [direction_eval_scale hL n]
    exact ht
  change IntervalIntegrable g volume (-L) L
  apply (IntervalIntegrable.comp_mul_left_iff (f := g) (a := -L) (b := L) hL.ne').mp
  rw [he,neg_div,div_self hL.ne']
  exact (RHTuckPolynomial.quotient_integrable (directionPoly 1 n) hu).const_mul _
end RHTuckScaledEigen
