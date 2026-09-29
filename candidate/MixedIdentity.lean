import ExpectedScaled
import PolynomialSymmetry
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHTuckMixed

noncomputable def mixedDifference (f : ℝ → ℂ) (p : Polynomial ℂ) (z : ℝ × ℝ) : ℂ :=
  conj (f z.1 - f z.2) * RHTuckPolynomial.quotient p z.1 z.2

lemma quotient_swap (p : Polynomial ℂ) (x y : ℝ) :
    RHTuckPolynomial.quotient p y x = - RHTuckPolynomial.quotient p x y := by
  simp only [RHTuckPolynomial.quotient, abs_sub_comm y x]
  ring

theorem difference_integrable {L : ℝ} (f : ℝ → ℂ) (p : Polynomial ℂ)
    (ha : Integrable (fun z : ℝ × ℝ => conj (f z.1) * RHTuckPolynomial.quotient p z.1 z.2)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) :
    Integrable (mixedDifference f p)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  apply (ha.add ha.swap).congr
  filter_upwards [] with z
  simp only [Pi.add_apply, Function.comp_apply, Prod.fst_swap, Prod.snd_swap,
    mixedDifference, map_sub]
  rw [quotient_swap p z.2 z.1]
  ring

theorem integral_difference {L : ℝ} (f : ℝ → ℂ) (p : Polynomial ℂ)
    (ha : Integrable (fun z : ℝ × ℝ => conj (f z.1) * RHTuckPolynomial.quotient p z.1 z.2)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) :
    (∫ z, mixedDifference f p z ∂((volume.restrict (Icc (-L) L)).prod
      (volume.restrict (Icc (-L) L)))) =
    2 * ∫ x in Icc (-L) L, conj (f x) *
      (∫ y in Icc (-L) L, RHTuckPolynomial.quotient p x y) := by
  let μ := volume.restrict (Icc (-L) L)
  let g : ℝ × ℝ → ℂ := fun z => conj (f z.1) * RHTuckPolynomial.quotient p z.1 z.2
  have he : mixedDifference f p = fun z => g z + g z.swap := by
    funext z
    simp only [mixedDifference, g, map_sub, Prod.fst_swap, Prod.snd_swap]
    rw [quotient_swap p z.2 z.1]
    ring
  rw [he]
  rw [integral_add (f := fun z => g z) (g := fun z => g z.swap) ha ha.swap]
  rw [integral_prod_swap (μ := μ) (ν := μ) g]
  have hfub := integral_integral (f := fun x y : ℝ => conj (f x) * RHTuckPolynomial.quotient p x y) ha
  have hi : (∫ z, g z ∂(μ.prod μ)) =
      ∫ x, conj (f x) * (∫ y, RHTuckPolynomial.quotient p x y ∂μ) ∂μ := by
    rw [← hfub]
    apply integral_congr_ae
    filter_upwards [] with x
    exact integral_const_mul _ _
  change (∫ z, g z ∂(μ.prod μ)) + (∫ z, g z ∂(μ.prod μ)) = _
  rw [hi]
  ring

theorem integral_direction {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (n : ℕ)
    (ha : Integrable (fun z : ℝ × ℝ => conj (f z.1) *
      RHTuckPolynomial.quotient (RHLegendreDirections.directionPoly L n) z.1 z.2)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) :
    (1/4:ℂ) * (∫ z, mixedDifference f (RHLegendreDirections.directionPoly L n) z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (harmonic n:ℂ) * (∫ x in Icc (-L) L,
        conj (f x) * (RHLegendreDirections.directionPoly L n).eval (x:ℂ)) := by
  rw [integral_difference f _ ha]
  have he : (∫ x in Icc (-L) L, conj (f x) *
      (∫ y in Icc (-L) L, RHTuckPolynomial.quotient (RHLegendreDirections.directionPoly L n) x y)) =
      (2*(harmonic n:ℂ)) * (∫ x in Icc (-L) L,
        conj (f x) * (RHLegendreDirections.directionPoly L n).eval (x:ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    change conj (f x) * (∫ y in (-L)..L,
      ((RHLegendreDirections.directionPoly L n).eval (x:ℂ)-
      (RHLegendreDirections.directionPoly L n).eval (y:ℂ))/((|x-y|:ℝ):ℂ)) = _
    rw [(RHExpected0276.actual_scaled_direction hL n hx).2]
    ring
  rw [he]
  ring
end RHTuckMixed
