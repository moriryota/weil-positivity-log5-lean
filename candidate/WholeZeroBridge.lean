import RealAutocorr

/- Exact full-zero target, with the half-width convention made explicit.
No positivity assertion or external numerical certificate is assumed here. -/
namespace RHLog5Bridge
open Real MeasureTheory RH_LiteratureBridge

noncomputable def halfWidth : ℝ := Real.log 5 / 2

lemma halfWidth_pos : 0 < halfWidth := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma twice_halfWidth : 2 * halfWidth = Real.log 5 := by
  unfold halfWidth
  ring

/-- Endpoint theorem for every real C¹ test, including non-even tests. -/
theorem whole_zero_endpoint (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand (fun x => (f x : ℂ))
        (fun x => (f x : ℂ)) (ρ : ℂ)) ∧
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      W_real (Real.log 5) (real_autocorr f) := by
  simpa only [twice_halfWidth] using
    weil_quad_form_re_eq_W_real f halfWidth_pos hf hsupp

/-- Smaller supports use the endpoint formula by inclusion, not induction. -/
theorem whole_zero_of_support_le (f : ℝ → ℝ) {L : ℝ}
    (hL : L ≤ halfWidth) (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ L) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand (fun x => (f x : ℂ))
        (fun x => (f x : ℂ)) (ρ : ℂ)) ∧
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      W_real (Real.log 5) (real_autocorr f) := by
  exact whole_zero_endpoint f hf (fun x hx => (hsupp x hx).trans hL)

lemma autocorr_zero (f : ℝ → ℝ) : real_autocorr f 0 = ∫ x, (f x)^2 := by
  simp [real_autocorr, pow_two]

/-- Fix the Gamma sign and the endpoint tail before introducing the spatial energy. -/
theorem W_real_deficit (b : ℝ) (h : ℝ → ℝ) :
    W_real b h =
      ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) * h 0 +
      RH_GammaFinalFormula.T_tail b * h 0 +
      (∫ x in (0 : ℝ)..b, (h 0 - h x) * RH_GammaFinalFormula.K_kernel x) +
      P_pole b h - S_prime h := by
  have heq : (∫ x in (0 : ℝ)..b, (h 0 - h x) * RH_GammaFinalFormula.K_kernel x) =
      -(∫ x in (0 : ℝ)..b, (h x - h 0) * RH_GammaFinalFormula.K_kernel x) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [heq, W_real, A_arch]
  ring

/-- The only hypothesis not discharged here is positivity of the correctly matched real form. -/
theorem transfer_real_positivity
    (hpos : ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      (∀ x, f x ≠ 0 → |x| ≤ halfWidth) →
      0 ≤ W_real (Real.log 5) (real_autocorr f))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) :
    0 ≤ (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re := by
  rw [(whole_zero_endpoint f hf hsupp).2]
  exact hpos f hf hsupp
end RHLog5Bridge
