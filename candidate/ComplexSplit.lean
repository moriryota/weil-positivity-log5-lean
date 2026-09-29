import ComplexFrequency

namespace RHComplexFrequency
open Real MeasureTheory Set Zeta23
open scoped ComplexConjugate

lemma paired_square (a b : ℂ) :
    (a+Complex.I*b)*conj (a+Complex.I*b) +
      (conj a+Complex.I*conj b)*conj (conj a+Complex.I*conj b) =
      2*(a*conj a+b*conj b) := by
  simp only [map_add,map_mul,Complex.conj_I,Complex.conj_conj]
  ring_nf <;> simp [Complex.I_sq] <;> ring

noncomputable def density (L : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  paperFT f t*conj (paperFT f t)*(nuX (Real.exp L) t:ℂ)

lemma density_pair {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (L t : ℝ) :
    density L f t+density L f (-t) =
      2*(density L (fun x => ((f x).re:ℂ)) t+density L (fun x => ((f x).im:ℂ)) t) := by
  have hr : paperFT (fun x => ((f x).re:ℂ)) ((-t:ℝ):ℂ) =
      conj (paperFT (fun x => ((f x).re:ℂ)) (t:ℂ)) := by
    simpa only [Complex.conj_ofReal,Complex.ofReal_neg] using
      (Zeta23.Taper.conj_paperFT_ofReal (fun x => (f x).re) (t:ℂ)).symm
  have hi : paperFT (fun x => ((f x).im:ℂ)) ((-t:ℝ):ℂ) =
      conj (paperFT (fun x => ((f x).im:ℂ)) (t:ℂ)) := by
    simpa only [Complex.conj_ofReal,Complex.ofReal_neg] using
      (Zeta23.Taper.conj_paperFT_ofReal (fun x => (f x).im) (t:ℂ)).symm
  unfold density
  rw [paperFT_re_im hf hc (t:ℂ),paperFT_re_im hf hc ((-t:ℝ):ℂ),hr,hi,nuX_even_exp]
  linear_combination (paired_square (paperFT (fun x => ((f x).re:ℂ)) (t:ℂ))
    (paperFT (fun x => ((f x).im:ℂ)) (t:ℂ))) * (nuX (Real.exp L) t:ℂ)

lemma integral_of_pair {a u v : ℝ → ℂ} (ha : Integrable a) (hu : Integrable u)
    (hv : Integrable v) (he : ∀ t, a t+a (-t)=2*(u t+v t)) :
    (∫ t, a t) = (∫ t, u t)+(∫ t, v t) := by
  have han : Integrable (fun t => a (-t)) := ha.comp_neg
  have hleft : (∫ t, a t+a (-t)) = (∫ t,a t)+(∫ t,a (-t)) := integral_add ha han
  have hneg : (∫ t,a (-t)) = ∫ t,a t := integral_neg_eq_self a volume
  have hright : (∫ t, u t+v t) = (∫ t,u t)+(∫ t,v t) := integral_add hu hv
  have heq : (∫ t, a t+a (-t)) = ∫ t, (2:ℂ)*(u t+v t) :=
    integral_congr_ae (Filter.Eventually.of_forall he)
  rw [hleft,hneg,integral_const_mul,hright] at heq
  apply mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
  linear_combination heq

/-- Complex equality of diagonal Weil forms, not an assumed Hermitian cancellation. -/
theorem W_re_im {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ 2 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    zetaZeroConfig.W f f =
      zetaZeroConfig.W (fun x => ((f x).re:ℂ)) (fun x => ((f x).re:ℂ)) +
      zetaZeroConfig.W (fun x => ((f x).im:ℂ)) (fun x => ((f x).im:ℂ)) := by
  have hrd : ContDiff ℝ 2 (fun x => ((f x).re:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf)
  have hid : ContDiff ℝ 2 (fun x => ((f x).im:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf)
  have hrs : ∀ x, ((f x).re:ℂ) ≠ 0 → |x| ≤ L := by
    intro x hx
    apply re_support hs x
    intro hh
    exact hx (by rw [hh]; rfl)
  have his : ∀ x, ((f x).im:ℂ) ≠ 0 → |x| ≤ L := by
    intro x hx
    apply im_support hs x
    intro hh
    exact hx (by rw [hh]; rfl)
  have hff := frequency_package hL hf hs
  have hrr := frequency_package hL hrd hrs
  have hii := frequency_package hL hid his
  rw [hff.2.2,hrr.2.2,hii.2.2]
  exact integral_of_pair hff.2.1 hrr.2.1 hii.2.1
    (density_pair hf.continuous (compact_of_support hs) (2*L))
end RHComplexFrequency
