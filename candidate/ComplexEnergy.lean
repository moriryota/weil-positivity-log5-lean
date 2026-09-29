import ComplexFrequency
import ComplexSpatialParts

namespace RHComplexSpatial
open Real MeasureTheory Set RHAutocorrEnergy RHComplexFrequency

noncomputable def complexSpatialEnergy (f : ℝ → ℂ) : ℝ :=
  (1/4:ℝ)*∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| * ‖f x-f y‖^2

lemma real_spatial_product {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    spatialEnergy f = (1/4:ℝ)*∫ p : ℝ×ℝ,
      RH_GammaFinalFormula.K_kernel |p.1| *(f p.2-f (p.2-p.1))^2 ∂(volume.prod volume) := by
  have hchange (x : ℝ) :
      (∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(f x-f y)^2) =
      ∫ s, RH_GammaFinalFormula.K_kernel |s| *(f x-f (x-s))^2 := by
    have ht := integral_sub_left_eq_self (fun s => RH_GammaFinalFormula.K_kernel |s| *
      (f x-f (x-s))^2) volume x
    simpa only [sub_sub_self] using ht
  have hp : (∫ p : ℝ×ℝ, RH_GammaFinalFormula.K_kernel |p.1| *
      (f p.2-f (p.2-p.1))^2 ∂(volume.prod volume)) =
      ∫ x, ∫ s, RH_GammaFinalFormula.K_kernel |s| *(f x-f (x-s))^2 :=
    integral_prod_symm _ (displacement_product_integrable hL hf hs)
  unfold spatialEnergy
  simp_rw [hchange]
  rw [hp]

lemma complex_product_integrable {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    Integrable (fun p : ℝ×ℝ => RH_GammaFinalFormula.K_kernel |p.1| *
      ‖f p.2-f (p.2-p.1)‖^2) (volume.prod volume) := by
  have hr := displacement_product_integrable hL (Complex.reCLM.contDiff.comp hf) (re_support hs)
  have hi := displacement_product_integrable hL (Complex.imCLM.contDiff.comp hf) (im_support hs)
  apply (hr.add hi).congr
  apply Filter.Eventually.of_forall
  intro p
  change RH_GammaFinalFormula.K_kernel |p.1| * ((f p.2).re-(f (p.2-p.1)).re)^2 +
    RH_GammaFinalFormula.K_kernel |p.1| * ((f p.2).im-(f (p.2-p.1)).im)^2 =
    RH_GammaFinalFormula.K_kernel |p.1| * ‖f p.2-f (p.2-p.1)‖^2
  rw [norm_sq_parts]
  simp only [Complex.sub_re,Complex.sub_im]
  ring

lemma complex_spatial_product {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    complexSpatialEnergy f = (1/4:ℝ)*∫ p : ℝ×ℝ,
      RH_GammaFinalFormula.K_kernel |p.1| * ‖f p.2-f (p.2-p.1)‖^2 ∂(volume.prod volume) := by
  have hchange (x : ℝ) :
      (∫ y, RH_GammaFinalFormula.K_kernel |x-y| * ‖f x-f y‖^2) =
      ∫ s, RH_GammaFinalFormula.K_kernel |s| * ‖f x-f (x-s)‖^2 := by
    have ht := integral_sub_left_eq_self (fun s => RH_GammaFinalFormula.K_kernel |s| *
      ‖f x-f (x-s)‖^2) volume x
    simpa only [sub_sub_self] using ht
  have hp : (∫ p : ℝ×ℝ, RH_GammaFinalFormula.K_kernel |p.1| *
      ‖f p.2-f (p.2-p.1)‖^2 ∂(volume.prod volume)) =
      ∫ x, ∫ s, RH_GammaFinalFormula.K_kernel |s| * ‖f x-f (x-s)‖^2 :=
    integral_prod_symm _ (complex_product_integrable hL hf hs)
  unfold complexSpatialEnergy
  simp_rw [hchange]
  rw [hp]

lemma complex_spatial_parts {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    complexSpatialEnergy f = spatialEnergy (fun x => (f x).re)+spatialEnergy (fun x => (f x).im) := by
  have hrd : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hid : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hr := displacement_product_integrable hL hrd (re_support hs)
  have hi := displacement_product_integrable hL hid (im_support hs)
  have heq : (fun p : ℝ×ℝ => RH_GammaFinalFormula.K_kernel |p.1| * ‖f p.2-f (p.2-p.1)‖^2) =
      (fun p : ℝ×ℝ => RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).re-(f (p.2-p.1)).re)^2 +
        RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).im-(f (p.2-p.1)).im)^2) := by
    funext p
    rw [norm_sq_parts]
    simp only [Complex.sub_re,Complex.sub_im]
    ring
  have hadd : (∫ p : ℝ×ℝ, RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).re-(f (p.2-p.1)).re)^2 +
      RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).im-(f (p.2-p.1)).im)^2 ∂(volume.prod volume)) =
      (∫ p : ℝ×ℝ, RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).re-(f (p.2-p.1)).re)^2 ∂(volume.prod volume)) +
      (∫ p : ℝ×ℝ, RH_GammaFinalFormula.K_kernel |p.1| *((f p.2).im-(f (p.2-p.1)).im)^2 ∂(volume.prod volume)) :=
    integral_add hr hi
  rw [complex_spatial_product hL hf hs,real_spatial_product hL hrd (re_support hs),
    real_spatial_product hL hid (im_support hs),heq,hadd]
  ring
end RHComplexSpatial
