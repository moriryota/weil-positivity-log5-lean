import RealSpatialEndpoint
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete

namespace RHComplexFrequency
open Real MeasureTheory Set Zeta23
open scoped ComplexConjugate

lemma PiX_even_exp (L t : ℝ) : PiX (Real.exp L) (-t) = PiX (Real.exp L) t := by
  have hc : conj ((1/2:ℂ)+Complex.I*(t:ℂ)) = (1/2:ℂ)+Complex.I*((-t:ℝ):ℂ) := by
    simp only [map_add,map_div₀,map_one,map_ofNat,map_mul,Complex.conj_I,
      Complex.conj_ofReal,Complex.ofReal_neg]
    ring
  have he : (((Real.exp L:ℝ):ℂ)^((1/2:ℂ)+Complex.I*((-t:ℝ):ℂ))-1) /
      ((1/2:ℂ)+Complex.I*((-t:ℝ):ℂ)) =
      conj ((((Real.exp L:ℝ):ℂ)^((1/2:ℂ)+Complex.I*(t:ℂ))-1) /
        ((1/2:ℂ)+Complex.I*(t:ℂ))) := by
    rw [EF.exp_cpow, EF.exp_cpow,map_div₀,map_sub,map_one,← Complex.exp_conj,map_mul,
      Complex.conj_ofReal,hc]
  unfold PiX
  dsimp only
  rw [he,Complex.conj_re]
  simp only [neg_sq]

lemma PX_even (X t : ℝ) : PX X (-t) = PX X t := by
  unfold PX
  simp only [neg_mul,Real.cos_neg]

lemma nuX_even_exp (L t : ℝ) : nuX (Real.exp L) (-t) = nuX (Real.exp L) t := by
  unfold nuX
  rw [Zeta23.mu_even,PiX_even_exp,PX_even]

lemma compact_of_support {f : ℝ → ℂ} {L : ℝ}
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  exact abs_le.mp (hs x hx)

lemma re_support {f : ℝ → ℂ} {L : ℝ} (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    ∀ x, (f x).re ≠ 0 → |x| ≤ L := by
  intro x hx
  apply hs x
  intro hh
  exact hx (by rw [hh]; rfl)

lemma im_support {f : ℝ → ℂ} {L : ℝ} (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    ∀ x, (f x).im ≠ 0 → |x| ≤ L := by
  intro x hx
  apply hs x
  intro hh
  exact hx (by rw [hh]; rfl)

/-- Linear decomposition of the Fourier transform, with compact-support integrability. -/
lemma paperFT_re_im {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    paperFT f z = paperFT (fun x => ((f x).re:ℂ)) z +
      Complex.I * paperFT (fun x => ((f x).im:ℂ)) z := by
  have hrc : HasCompactSupport (fun x => ((f x).re:ℂ)) := by
    apply hc.mono
    intro x hx hh
    apply hx
    simp [hh]
  have hic : HasCompactSupport (fun x => ((f x).im:ℂ)) := by
    apply hc.mono
    intro x hx hh
    apply hx
    simp [hh]
  have hr : Integrable (fun x => ((f x).re:ℂ)*Complex.exp (Complex.I*z*(x:ℂ))) :=
    ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf)).mul
      (by fun_prop)).integrable_of_hasCompactSupport hrc.mul_right
  have hi : Integrable (fun x => Complex.I*(((f x).im:ℂ)*Complex.exp (Complex.I*z*(x:ℂ)))) :=
    (continuous_const.mul ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf)).mul
      (by fun_prop))).integrable_of_hasCompactSupport (hic.mul_right.mul_left)
  unfold paperFT
  rw [← integral_const_mul]
  have hadd : (∫ x, ((f x).re:ℂ)*Complex.exp (Complex.I*z*(x:ℂ)) +
      Complex.I*(((f x).im:ℂ)*Complex.exp (Complex.I*z*(x:ℂ)))) =
      (∫ x, ((f x).re:ℂ)*Complex.exp (Complex.I*z*(x:ℂ))) +
      (∫ x, Complex.I*(((f x).im:ℂ)*Complex.exp (Complex.I*z*(x:ℂ)))) := integral_add hr hi
  rw [← hadd]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    linear_combination -(Complex.re_add_im (f x)) * Complex.exp (Complex.I*z*(x:ℂ)))

/-- This is the unconditional upstream package; C² is an explicit hypothesis. -/
theorem frequency_package {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 2 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    Integrable (fun t : ℝ => paperFT f t*conj (paperFT f t)*(nuX (Real.exp (2*L)) t:ℂ)) ∧
    zetaZeroConfig.W f f = ∫ t : ℝ, paperFT f t*conj (paperFT f t)*(nuX (Real.exp (2*L)) t:ℂ) := by
  have hts : tsupport f ⊆ Icc (-L) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact abs_le.mp (hs x hx)
  have hts' : tsupport f ⊆ Icc (-((2*L)/2)) ((2*L)/2) := by
    simpa only [mul_div_cancel_left₀ L (by norm_num : (2:ℝ) ≠ 0)] using hts
  exact (EF.explicitFormulaPaper_of_lit zetaZeroConfig WeilEF.EF_lit_zetaZeroConfig
    Zeta23.gammaFacts) (2*L) (by linarith) f f hf hf hts' hts'
end RHComplexFrequency
