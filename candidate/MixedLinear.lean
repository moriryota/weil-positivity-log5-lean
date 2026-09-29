import ExpectedMixed
open Polynomial MeasureTheory Set Filter
open scoped ComplexConjugate
namespace RHFiniteMixed
noncomputable def value (L : ℝ) (f : ℝ → ℂ) (p : Polynomial ℂ) : ℂ :=
  (1/4:ℂ) * ∫ z, RHTuckMixed.mixedDifference f p z
    ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))

lemma difference_add (f : ℝ → ℂ) (p q : Polynomial ℂ) :
    RHTuckMixed.mixedDifference f (p+q) = fun z =>
      RHTuckMixed.mixedDifference f p z+RHTuckMixed.mixedDifference f q z := by
  funext z
  simp only [RHTuckMixed.mixedDifference,RHTuckPolynomial.quotient,Polynomial.eval_add]
  ring
lemma difference_smul (f : ℝ → ℂ) (p : Polynomial ℂ) (c : ℂ) :
    RHTuckMixed.mixedDifference f (c • p) = fun z => c * RHTuckMixed.mixedDifference f p z := by
  funext z
  simp only [RHTuckMixed.mixedDifference,RHTuckPolynomial.quotient,Polynomial.eval_smul,smul_eq_mul]
  ring
noncomputable def linear (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun := value L f
  map_add' p q := by
    unfold value
    rw [difference_add,integral_add
      (f := RHTuckMixed.mixedDifference f p) (g := RHTuckMixed.mixedDifference f q)
      (RHExpected0285.actual_polynomial_mixed f p).1 (RHExpected0285.actual_polynomial_mixed f q).1]
    ring
  map_smul' c p := by
    simp only [RingHom.id_apply,smul_eq_mul]
    unfold value
    rw [difference_smul,integral_const_mul]
    ring

lemma value_congr {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Icc (-L) L)] g) (p : Polynomial ℂ) :
    value L f p = value L g p := by
  unfold value
  congr 1
  apply integral_congr_ae
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae_eq h, (Measure.quasiMeasurePreserving_snd).ae_eq h] with z hx hy
  simp only [Function.comp_apply] at hx hy
  simp only [RHTuckMixed.mixedDifference,hx,hy]

lemma real_value (L : ℝ) (f : ℝ → ℂ) (p : Polynomial ℂ)
    (hi : Integrable (RHTuckMixed.mixedDifference f p)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) :
    (value L f p).re = (1/4:ℝ) * ∫ z, (RHTuckMixed.mixedDifference f p z).re
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  unfold value
  have hr : (∫ z, (RHTuckMixed.mixedDifference f p z).re
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) =
      (∫ z, RHTuckMixed.mixedDifference f p z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))).re :=
    Complex.reCLM.integral_comp_comm hi
  rw [hr]
  norm_num [Complex.mul_re]
end RHFiniteMixed
