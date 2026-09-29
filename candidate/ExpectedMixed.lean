import MixedIdentity
import MixedIntegrable
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHExpected0285

theorem actual_polynomial_mixed {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (p : Polynomial ℂ) :
    Integrable (RHTuckMixed.mixedDifference f p)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) ∧
    (1/4:ℂ) * (∫ z, RHTuckMixed.mixedDifference f p z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (1/2:ℂ) * (∫ x in Icc (-L) L, conj (f x) *
        (∫ y in Icc (-L) L, RHTuckPolynomial.quotient p x y)) := by
  have hf : Integrable (fun x => f x) (volume.restrict (Icc (-L) L)) :=
    (Lp.memLp f).integrable (by norm_num)
  have ha := RHTuckMixed.mixed_integrable hf p
  refine ⟨RHTuckMixed.difference_integrable f p ha, ?_⟩
  rw [RHTuckMixed.integral_difference f p ha]
  ring

theorem actual_L2_mixed {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (n : ℕ) :
    Integrable (RHTuckMixed.mixedDifference f (RHLegendreDirections.directionPoly L n))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) ∧
    (1/4:ℂ) * (∫ z, RHTuckMixed.mixedDifference f (RHLegendreDirections.directionPoly L n) z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (harmonic n:ℂ) * (∫ x in Icc (-L) L,
        conj (f x) * (RHLegendreDirections.directionPoly L n).eval (x:ℂ)) := by
  have hf : Integrable (fun x => f x) (volume.restrict (Icc (-L) L)) :=
    (Lp.memLp f).integrable (by norm_num)
  have ha := RHTuckMixed.mixed_integrable hf (RHLegendreDirections.directionPoly L n)
  exact ⟨RHTuckMixed.difference_integrable f _ ha,
    RHTuckMixed.integral_direction hL f n ha⟩
theorem actual_mixed_package {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    (∀ p : Polynomial ℂ,
      Integrable (RHTuckMixed.mixedDifference f p)
        ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) ∧
      (1/4:ℂ) * (∫ z, RHTuckMixed.mixedDifference f p z
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (1/2:ℂ) * (∫ x in Icc (-L) L, conj (f x) *
        (∫ y in Icc (-L) L, RHTuckPolynomial.quotient p x y))) ∧
    (∀ n : ℕ,
      (1/4:ℂ) * (∫ z, RHTuckMixed.mixedDifference f (RHLegendreDirections.directionPoly L n) z
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (harmonic n:ℂ) * (∫ x in Icc (-L) L,
        conj (f x) * (RHLegendreDirections.directionPoly L n).eval (x:ℂ))) := by
  exact ⟨fun p => actual_polynomial_mixed f p, fun n => (actual_L2_mixed hL f n).2⟩
end RHExpected0285


