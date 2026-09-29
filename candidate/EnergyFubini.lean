import AutocorrEnergy

namespace RHAutocorrEnergy
open Real MeasureTheory Set RH_LiteratureBridge

lemma integrable_of_even_Ioi {g : ℝ → ℝ} (he : ∀ s, g (-s)=g s)
    (hi : IntegrableOn g (Ioi (0:ℝ))) : Integrable g := by
  have hn : IntegrableOn g (Iic (0:ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  have hu := hn.union hi
  rwa [Iic_union_Ioi, integrableOn_univ] at hu

lemma kernel_abs_nonneg (s : ℝ) : 0 ≤ RH_GammaFinalFormula.K_kernel |s| := by
  unfold RH_GammaFinalFormula.K_kernel RH_GammaSqrtBound.K_kernel
  exact div_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr (abs_nonneg s))

lemma autocorr_abs (f : ℝ → ℝ) (s : ℝ) : real_autocorr f |s| = real_autocorr f s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, real_autocorr_even]

lemma square_integral_eq_twice {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s : ℝ) :
    (∫ t, (f t-f (t-s))^2) = 2*(real_autocorr f 0-real_autocorr f s) := by
  linarith [autocorr_deficit hf hc s]

/-- Absolute integrability of the displacement-coordinate double integrand. -/
theorem displacement_product_integrable {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    Integrable (fun p : ℝ × ℝ => RH_GammaFinalFormula.K_kernel |p.1| *
      (f p.2-f (p.2-p.1))^2) (volume.prod volume) := by
  have hc := compact_real hs
  have hm : Measurable (fun p : ℝ × ℝ => RH_GammaFinalFormula.K_kernel |p.1| *
      (f p.2-f (p.2-p.1))^2) := by
    have hfc := hf.continuous.measurable
    unfold RH_GammaFinalFormula.K_kernel RH_GammaSqrtBound.K_kernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro s
    change Integrable (fun y => RH_GammaFinalFormula.K_kernel |s| * (f y-f (y-s))^2)
    exact (difference_sq_integrable hf.continuous hc s).const_mul (RH_GammaFinalFormula.K_kernel |s|)
  · have he : ∀ s, (RH_GammaFinalFormula.K_kernel |-s| * (∫ t, (f t-f (t- -s))^2)) =
        RH_GammaFinalFormula.K_kernel |s| * (∫ t, (f t-f (t-s))^2) := by
      intro s
      simp only [abs_neg, square_integral_eq_twice hf.continuous hc, real_autocorr_even]
    have hp : IntegrableOn (fun s => RH_GammaFinalFormula.K_kernel |s| *
        (∫ t, (f t-f (t-s))^2)) (Ioi (0:ℝ)) := by
      apply (weighted_difference_integrable hL hf hs).congr_fun _ measurableSet_Ioi
      intro s hsp
      dsimp only
      rw [abs_of_pos (show 0 < s from hsp)]
    have hi := integrable_of_even_Ioi he hp
    apply hi.congr
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kernel_abs_nonneg s) (sq_nonneg _))])

noncomputable def spatialEnergy (f : ℝ → ℝ) : ℝ :=
  (1/4:ℝ) * ∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| * (f x-f y)^2

/-- Fubini is justified by the preceding product-integrability theorem. -/
theorem spatial_eq_displacement {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    spatialEnergy f = displacementEnergy f := by
  have hc := compact_real hs
  have hchange (x : ℝ) :
      (∫ y, RH_GammaFinalFormula.K_kernel |x-y| * (f x-f y)^2) =
      ∫ s, RH_GammaFinalFormula.K_kernel |s| * (f x-f (x-s))^2 := by
    have ht := integral_sub_left_eq_self (fun s => RH_GammaFinalFormula.K_kernel |s| *
      (f x-f (x-s))^2) volume x
    simpa only [sub_sub_self] using ht
  unfold spatialEnergy
  simp_rw [hchange]
  have hswap : (∫ s, ∫ t, RH_GammaFinalFormula.K_kernel |s| * (f t-f (t-s))^2) =
      ∫ t, ∫ s, RH_GammaFinalFormula.K_kernel |s| * (f t-f (t-s))^2 :=
    integral_integral_swap (displacement_product_integrable hL hf hs)
  rw [← hswap]
  simp_rw [integral_const_mul, square_integral_eq_twice hf.continuous hc]
  have heq : (fun s => RH_GammaFinalFormula.K_kernel |s| *
      (2*(real_autocorr f 0-real_autocorr f s))) =
      (fun s => 2*(RH_GammaFinalFormula.K_kernel |s| *
        (real_autocorr f 0-real_autocorr f |s|))) := by
    funext s
    rw [autocorr_abs]
    ring
  have habs : (∫ s, RH_GammaFinalFormula.K_kernel |s| *
      (real_autocorr f 0-real_autocorr f |s|)) =
      2 * ∫ s in Ioi (0:ℝ), RH_GammaFinalFormula.K_kernel s *
        (real_autocorr f 0-real_autocorr f s) :=
    integral_comp_abs (f := fun s => RH_GammaFinalFormula.K_kernel s *
      (real_autocorr f 0-real_autocorr f s))
  rw [heq, integral_const_mul, habs, displacement_eq_deficit hf.continuous hc]
  ring

theorem whole_zero_eq_spatial {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi) * (∫ x, (f x)^2) +
      spatialEnergy f + P_pole (2*L) (real_autocorr f) - S_prime (real_autocorr f) := by
  rw [spatial_eq_displacement hL hf hs]
  exact whole_zero_eq_displacement hL hf hs
end RHAutocorrEnergy
