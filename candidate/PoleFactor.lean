import AutocorrEnergy

namespace RHPoleFactor
open Real MeasureTheory Set RH_LiteratureBridge
open scoped ComplexConjugate

lemma paperFT_imaginary (f : ℝ → ℝ) (a : ℝ) :
    Zeta23.paperFT (fun x => (f x : ℂ)) (Complex.I*(a:ℂ)) =
      ((∫ x, f x * Real.exp (-a*x) : ℝ) : ℂ) := by
  unfold Zeta23.paperFT
  rw [← integral_ofReal_C]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have he : Complex.I*(Complex.I*(a:ℂ))*(x:ℂ) = ((-a*x:ℝ):ℂ) := by
      calc
        _ = (Complex.I*Complex.I)*((a:ℂ)*(x:ℂ)) := by ring
        _ = _ := by simp [Complex.I_mul_I]
    dsimp only
    rw [he, ← Complex.ofReal_exp]
    push_cast
    rfl)

/-- Factor the pole term via the existing Fourier transform of a convolution. -/
theorem pole_autocorr_laplace {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    P_pole (2*L) (real_autocorr f) =
      2*(∫ x, f x*Real.exp (x/2))*(∫ x, f x*Real.exp (-x/2)) := by
  have hp := pole_term_bridge (by linarith : 0 < 2*L)
    (real_autocorr_contDiff hf hs).continuous (real_autocorr_even f)
    (tsupport_subset_Icc_of_supp_abs_le (real_autocorr_supp_bound hL hs))
  rw [real_autocorr_eq_weilTest] at hp
  have hfc : Continuous (fun x => (f x : ℂ)) := Complex.continuous_ofReal.comp hf.continuous
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) := hasCompactSupport_of_supp_abs_le hs
  rw [Zeta23.EF.paperFT_weilTest hfc hfc hcc hcc,
    Zeta23.EF.paperFT_weilTest hfc hfc hcc hcc] at hp
  have hip : Complex.I/2 = Complex.I*((1/2:ℝ):ℂ) := by push_cast; ring
  have him : -Complex.I/2 = Complex.I*((-1/2:ℝ):ℂ) := by push_cast; ring
  have hcp : conj (Complex.I/2) = -Complex.I/2 := by simp [map_ofNat]
  have hcm : conj (-Complex.I/2) = Complex.I/2 := by simp [map_ofNat]
  rw [hcp,hcm,hip,him,paperFT_imaginary,paperFT_imaginary] at hp
  have hp' : ∀ x : ℝ, -(-1/2)*x = x/2 := by intro x; ring
  have hm' : ∀ x : ℝ, -(1/2)*x = -x/2 := by intro x; ring
  simp only [hp',hm',Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_add,
    Complex.ofReal_re] at hp
  rw [← hp]
  ring
theorem pole_autocorr_cosh_sinh {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    P_pole (2*L) (real_autocorr f) =
      2*(∫ x, f x*Real.cosh (x/2))^2-2*(∫ x, f x*Real.sinh (x/2))^2 := by
  have hc := RHAutocorrEnergy.compact_real hs
  have hC : Integrable (fun x => f x*Real.cosh (x/2)) :=
    (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hS : Integrable (fun x => f x*Real.sinh (x/2)) :=
    (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hp : (∫ x, f x*Real.exp (x/2)) =
      (∫ x, f x*Real.cosh (x/2))+(∫ x, f x*Real.sinh (x/2)) := by
    calc
      _ = ∫ x, (f x*Real.cosh (x/2)+f x*Real.sinh (x/2)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only; rw [← mul_add, Real.cosh_add_sinh])
      _ = _ := integral_add hC hS
  have hm : (∫ x, f x*Real.exp (-x/2)) =
      (∫ x, f x*Real.cosh (x/2))-(∫ x, f x*Real.sinh (x/2)) := by
    calc
      _ = ∫ x, (f x*Real.cosh (x/2)-f x*Real.sinh (x/2)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only; rw [← mul_sub, Real.cosh_sub_sinh, neg_div])
      _ = _ := integral_sub hC hS
  rw [pole_autocorr_laplace hL hf hs,hp,hm]
  ring
end RHPoleFactor
