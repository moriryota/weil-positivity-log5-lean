import RealSpatialEndpoint

namespace RHComplexSpatial
open Real MeasureTheory Set RH_LiteratureBridge RHAutocorrEnergy
open scoped ComplexConjugate

lemma norm_sq_parts (z : ℂ) : ‖z‖^2=z.re^2+z.im^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring

lemma re_compact {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun x => (f x).re) := by
  apply hc.mono
  intro x hx hh
  exact hx (by dsimp only; rw [hh]; rfl)

lemma im_compact {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun x => (f x).im) := by
  apply hc.mono
  intro x hx hh
  exact hx (by dsimp only; rw [hh]; rfl)

lemma integral_norm_sq_parts {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x, ‖f x‖^2) = (∫ x, (f x).re^2)+(∫ x, (f x).im^2) := by
  have hr : Integrable (fun x => (f x).re^2) := ((Complex.continuous_re.comp hf).pow 2).integrable_of_hasCompactSupport
    (square_compact (re_compact hc))
  have hi : Integrable (fun x => (f x).im^2) := ((Complex.continuous_im.comp hf).pow 2).integrable_of_hasCompactSupport
    (square_compact (im_compact hc))
  simp_rw [norm_sq_parts]
  exact integral_add hr hi

lemma norm_integral_weight_parts {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (w : ℝ → ℝ) (hw : Continuous w) :
    ‖∫ x, f x*(w x:ℂ)‖^2 = (∫ x, (f x).re*w x)^2+(∫ x, (f x).im*w x)^2 := by
  have hi : Integrable (fun x => f x*(w x:ℂ)) :=
    (hf.mul (Complex.continuous_ofReal.comp hw)).integrable_of_hasCompactSupport hc.mul_right
  have hr : (∫ x, (f x*(w x:ℂ)).re) = (∫ x, f x*(w x:ℂ)).re := integral_re hi
  have him : (∫ x, (f x*(w x:ℂ)).im) = (∫ x, f x*(w x:ℂ)).im := integral_im hi
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hr
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at him
  rw [norm_sq_parts,← hr,← him]

lemma autocorr_re_parts {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (s : ℝ) :
    (∫ t, f t*conj (f (t-s))).re =
      real_autocorr (fun t => (f t).re) s+real_autocorr (fun t => (f t).im) s := by
  have hi : Integrable (fun t => f t*conj (f (t-s))) :=
    (hf.mul ((hf.comp (continuous_id.sub continuous_const)).star)).integrable_of_hasCompactSupport hc.mul_right
  have he : (∫ t, (f t*conj (f (t-s))).re) = (∫ t, f t*conj (f (t-s))).re := integral_re hi
  have hrc := Complex.continuous_re.comp hf
  have hic := Complex.continuous_im.comp hf
  have hr : Integrable (fun t => (f t).re*(f (t-s)).re) :=
    (hrc.mul (hrc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport (re_compact hc).mul_right
  have him : Integrable (fun t => (f t).im*(f (t-s)).im) :=
    (hic.mul (hic.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport (im_compact hc).mul_right
  rw [← he]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add]
  exact integral_add hr him
end RHComplexSpatial
