import ProductComparison
import ExpectedMixed
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHComparisonIntegral
set_option maxHeartbeats 1000000

lemma norm_sub_square (a b : ℂ) :
    ‖a-b‖^2 = ‖a‖^2+‖b‖^2-2*(conj a*b).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma mixed_real (f : ℝ → ℂ) (p : Polynomial ℂ) (z : ℝ × ℝ) :
    (RHTuckMixed.mixedDifference f p z).re =
      |z.1-z.2|⁻¹ * (conj (f z.1-f z.2) * (p.eval (z.1:ℂ)-p.eval (z.2:ℂ))).re := by
  unfold RHTuckMixed.mixedDifference RHTuckPolynomial.quotient
  rw [← mul_div_assoc, Complex.div_ofReal_re]
  ring

lemma density_polynomial (p : Polynomial ℂ) :
    density (fun x => p.eval (x:ℂ)) =
      fun z => (RHTuckMixed.mixedDifference (fun x => p.eval (x:ℂ)) p z).re := by
  funext z
  rw [mixed_real, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  rfl

theorem polynomial_density_integrable (L : ℝ) (p : Polynomial ℂ) :
    Integrable (density (fun x => p.eval (x:ℂ)))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  have hp : Continuous (fun x : ℝ => p.eval (x:ℂ)) := by fun_prop
  have hi : Integrable (fun x : ℝ => p.eval (x:ℂ)) (volume.restrict (Icc (-L) L)) :=
    hp.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (-L) L))
  have ha := RHTuckMixed.mixed_integrable hi p
  rw [density_polynomial]
  exact Complex.reCLM.integrable_comp (RHTuckMixed.difference_integrable (L := L) (fun x : ℝ => p.eval (x:ℂ)) p ha)

lemma density_sub_polynomial (f : ℝ → ℂ) (p : Polynomial ℂ) :
    density (fun x => f x-p.eval (x:ℂ)) = fun z =>
      density f z+ density (fun x => p.eval (x:ℂ)) z -
        2*(RHTuckMixed.mixedDifference f p z).re := by
  funext z
  rw [mixed_real]
  unfold density
  have he : (f z.1-p.eval (z.1:ℂ))-(f z.2-p.eval (z.2:ℂ)) =
      (f z.1-f z.2)-(p.eval (z.1:ℂ)-p.eval (z.2:ℂ)) := by ring
  rw [he,norm_sub_square]
  ring

theorem residual_density_integrable {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (p : Polynomial ℂ) :
    Integrable (density (fun x => f x-p.eval (x:ℂ)))
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  have hm := (RHExpected0285.actual_polynomial_mixed f p).1
  rw [density_sub_polynomial]
  exact ((actual_Lp_integral f hf).1.add (polynomial_density_integrable L p)).sub
    ((Complex.reCLM.integrable_comp hm).const_mul 2)
end RHComparisonIntegral
