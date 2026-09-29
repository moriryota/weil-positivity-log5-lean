import FormDomain
open MeasureTheory Set Filter
open scoped ENNReal
namespace RHComparisonEnergy

noncomputable def kernel (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (|s|⁻¹)
noncomputable def energy (L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹ * ∫⁻ x in Icc (-L) L, ∫⁻ y in Icc (-L) L,
    kernel (x-y) * ENNReal.ofReal (‖f x-f y‖^2)

lemma energy_congr_ae {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Icc (-L) L)] g) : energy L f = energy L g := by
  unfold energy
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  rw [hx,hy]

noncomputable def intervalEnergy (L : ℝ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : ℝ≥0∞ := energy L f

def InDomain (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : Prop :=
  intervalEnergy L f < ⊤

lemma intervalEnergy_zero (L : ℝ) : intervalEnergy L 0 = 0 := by
  have h := energy_congr_ae (L := L) (Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (-L) L)))
  simpa [intervalEnergy, energy] using h

lemma energy_extend (L : ℝ) (f : ℝ → ℂ) :
    energy L (RHFormDomain.extend L f) = energy L f := by
  apply energy_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact indicator_of_mem hx f

/-- Kernel comparison is an explicit input; no unproved analytic bound is hidden. -/
theorem energy_le_original {L : ℝ} (f : ℝ → ℂ)
    (hk : ∀ x ∈ Icc (-L) L, ∀ y ∈ Icc (-L) L,
      kernel (x-y) ≤ RHFormDomain.kernel (x-y)) :
    energy L f ≤ RHFormDomain.energy (RHFormDomain.extend L f) := by
  rw [← energy_extend L f]
  unfold energy RHFormDomain.energy
  apply mul_le_mul' le_rfl
  calc
    (∫⁻ x in Icc (-L) L, ∫⁻ y in Icc (-L) L,
      kernel (x-y) * ENNReal.ofReal (‖RHFormDomain.extend L f x-RHFormDomain.extend L f y‖^2))
      ≤ ∫⁻ x in Icc (-L) L, ∫⁻ y in Icc (-L) L,
        RHFormDomain.kernel (x-y) * ENNReal.ofReal (‖RHFormDomain.extend L f x-RHFormDomain.extend L f y‖^2) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
          exact mul_le_mul' (hk x hx y hy) le_rfl
    _ ≤ ∫⁻ x, ∫⁻ y, RHFormDomain.kernel (x-y) *
        ENNReal.ofReal (‖RHFormDomain.extend L f x-RHFormDomain.extend L f y‖^2) := by
          apply le_trans (lintegral_mono (fun x => lintegral_mono' Measure.restrict_le_self le_rfl))
          exact lintegral_mono' Measure.restrict_le_self le_rfl

theorem domain_of_original {L : ℝ}
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (hf : RHFormDomain.InDomain L f)
    (hk : ∀ x ∈ Icc (-L) L, ∀ y ∈ Icc (-L) L,
      kernel (x-y) ≤ RHFormDomain.kernel (x-y)) : InDomain L f :=
  lt_of_le_of_lt (energy_le_original f hk) hf

lemma finite_toReal {L : ℝ} (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : InDomain L f) : ENNReal.ofReal (intervalEnergy L f).toReal = intervalEnergy L f :=
  ENNReal.ofReal_toReal (ne_of_lt hf)
end RHComparisonEnergy
