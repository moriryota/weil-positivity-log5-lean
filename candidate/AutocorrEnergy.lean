import WholeZeroBridge

namespace RHAutocorrEnergy
open Real MeasureTheory Set RH_LiteratureBridge

lemma compact_real {f : ℝ → ℝ} {L : ℝ}
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  exact abs_le.mp (hs x hx)

lemma shift_compact {f : ℝ → ℝ} (hc : HasCompactSupport f) (s : ℝ) :
    HasCompactSupport (fun t => f (t-s)) := by
  convert hc.comp_homeomorph (Homeomorph.addRight (-s)) using 1
  ext t
  simp [sub_eq_add_neg]

lemma square_compact {f : ℝ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun t => (f t)^2) := by
  apply hc.mono
  intro t ht
  simp only [Function.mem_support] at ht ⊢
  intro hz
  exact ht (by rw [hz]; norm_num)

lemma difference_sq_integrable {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s : ℝ) :
    Integrable (fun t => (f t-f (t-s))^2) := by
  exact ((hf.sub (hf.comp (continuous_id.sub continuous_const))).pow 2).integrable_of_hasCompactSupport
    (square_compact (hc.sub (shift_compact hc s)))

/-- Exact translation identity, with all three expansion terms integrable. -/
theorem autocorr_deficit {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s : ℝ) :
    real_autocorr f 0-real_autocorr f s =
      (1/2:ℝ) * ∫ t, (f t-f (t-s))^2 := by
  have hshift : Continuous (fun t => f (t-s)) := hf.comp (continuous_id.sub continuous_const)
  have hi : Integrable (fun t => (f t)^2) :=
    (hf.pow 2).integrable_of_hasCompactSupport (square_compact hc)
  have hj : Integrable (fun t => (f (t-s))^2) :=
    (hshift.pow 2).integrable_of_hasCompactSupport (square_compact (shift_compact hc s))
  have hk : Integrable (fun t => f t*f (t-s)) :=
    (hf.mul hshift).integrable_of_hasCompactSupport hc.mul_right
  have heq : (fun t => (f t-f (t-s))^2) =
      (fun t => (f t)^2+(f (t-s))^2-2*(f t*f (t-s))) := by
    funext t; ring
  have hsub : (∫ t, (f t)^2+(f (t-s))^2-2*(f t*f (t-s))) =
      (∫ t, (f t)^2+(f (t-s))^2)-(∫ t, 2*(f t*f (t-s))) :=
    integral_sub (hi.add hj) (hk.const_mul 2)
  have hadd : (∫ t, (f t)^2+(f (t-s))^2) = (∫ t, (f t)^2)+(∫ t, (f (t-s))^2) :=
    integral_add hi hj
  have htrans : (∫ t, (f (t-s))^2) = ∫ t, (f t)^2 :=
    integral_sub_right_eq_self (fun t : ℝ => (f t)^2) s
  rw [heq, hsub, hadd, integral_const_mul, htrans]
  rw [RHLog5Bridge.autocorr_zero]
  unfold real_autocorr
  ring

lemma autocorr_deficit_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s : ℝ) : 0 ≤ real_autocorr f 0-real_autocorr f s := by
  rw [autocorr_deficit hf hc s]
  exact mul_nonneg (by norm_num) (integral_nonneg (fun t => sq_nonneg _))

noncomputable def displacementEnergy (f : ℝ → ℝ) : ℝ :=
  (1/2:ℝ) * ∫ s in Ioi (0:ℝ), RH_GammaFinalFormula.K_kernel s *
    (∫ t, (f t-f (t-s))^2)

/-- Reuse the existing Gamma integrability theorem, instead of redoing its local estimates. -/
theorem weighted_difference_integrable {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    IntegrableOn (fun s => RH_GammaFinalFormula.K_kernel s *
      (∫ t, (f t-f (t-s))^2)) (Ioi (0:ℝ)) := by
  have hi := RH_GammaFourierBridge.integrable_rhs_kernel (real_autocorr f)
    (real_autocorr_contDiff hf hs) (real_autocorr_supp_bound hL hs) (real_autocorr_even f)
  have heq : (fun s => RH_GammaFinalFormula.K_kernel s * (∫ t, (f t-f (t-s))^2)) =
      (fun s => 2*(RH_GammaFinalFormula.K_kernel s *
        (real_autocorr f 0-real_autocorr f s))) := by
    funext s
    rw [autocorr_deficit hf.continuous (compact_real hs) s]
    ring
  rw [heq]
  exact hi.const_mul 2

lemma displacement_eq_deficit {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    displacementEnergy f = ∫ s in Ioi (0:ℝ), RH_GammaFinalFormula.K_kernel s *
      (real_autocorr f 0-real_autocorr f s) := by
  unfold displacementEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by dsimp only; rw [autocorr_deficit hf hc s]; ring)

/-- The actual full-zero form now uses the displacement energy, without an energy-equality assumption. -/
theorem whole_zero_eq_displacement {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    (Zeta23.zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re =
      ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi) * (∫ x, (f x)^2) +
      displacementEnergy f + P_pole (2*L) (real_autocorr f) - S_prime (real_autocorr f) := by
  rw [(weil_quad_form_re_eq_W_real f hL hf hs).2, RHLog5Bridge.W_real_deficit,
    displacement_eq_deficit hf.continuous (compact_real hs)]
  have hsplit := RH_GammaFinalFormula.integral_kernel_split_tail (real_autocorr f)
    (by linarith : 0 < 2*L) (real_autocorr_contDiff hf hs)
    (real_autocorr_supp_bound hL hs) (real_autocorr_even f)
  rw [hsplit, intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 2*L)]
  simp_rw [mul_comm (real_autocorr f 0-real_autocorr f _) (RH_GammaFinalFormula.K_kernel _)]
  rw [RHLog5Bridge.autocorr_zero]
  ring
end RHAutocorrEnergy
