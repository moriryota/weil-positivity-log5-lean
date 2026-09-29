import FormDomain
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain

lemma extend_memLp (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    MemLp (extend L f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp f)

/-- Actual zero extension into global L², rather than an untyped representative. -/
noncomputable def zeroExtensionLp (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : Lp ℂ 2 (volume : Measure ℝ) :=
  (extend_memLp L f).toLp (extend L f)

lemma zeroExtensionLp_coe (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    (zeroExtensionLp L f : ℝ → ℂ) =ᵐ[volume] extend L f :=
  MemLp.coeFn_toLp (extend_memLp L f)

lemma zeroExtensionLp_energy (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    energy (zeroExtensionLp L f) = intervalEnergy L f :=
  energy_congr_ae (zeroExtensionLp_coe L f)

lemma zeroExtensionLp_support (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    ∀ᵐ x ∂volume, x ∉ Icc (-L) L → zeroExtensionLp L f x = 0 := by
  filter_upwards [zeroExtensionLp_coe L f] with x hx hnot
  rw [hx]
  simp [extend,hnot]

lemma zeroExtensionLp_restrict (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    (zeroExtensionLp L f : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)] f := by
  have h : (zeroExtensionLp L f : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)] extend L f :=
    ae_restrict_of_ae (zeroExtensionLp_coe L f)
  exact h.trans (indicator_ae_eq_restrict measurableSet_Icc)
end RHFormDomain
