import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain

/-- Nonnegative kernel, including a harmless zero value on the diagonal. -/
noncomputable def kernel (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (|s|/2) / Real.sinh |s|)

/-- Extended energy: no conversion of infinity to a real number. -/
noncomputable def energy (f : ℝ → ℂ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹ * ∫⁻ x, ∫⁻ y, kernel (x-y) * ENNReal.ofReal (‖f x-f y‖^2)

lemma energy_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) : energy f = energy g := by
  unfold energy
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  rw [hx, hy]

lemma energy_zero : energy (0 : ℝ → ℂ) = 0 := by simp [energy]

noncomputable def extend (L : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Icc (-L) L).indicator f

lemma extend_congr_ae {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Icc (-L) L)] g) : extend L f =ᵐ[volume] extend L g := by
  exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp h

lemma energy_extend_congr_ae {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Icc (-L) L)] g) :
    energy (extend L f) = energy (extend L g) := energy_congr_ae (extend_congr_ae h)

/-- Interval L² elements already quotient out a.e. equality. -/
noncomputable def intervalEnergy (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : ℝ≥0∞ :=
  energy (extend L f)

def InDomain (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : Prop :=
  intervalEnergy L f < ⊤

lemma intervalEnergy_zero (L : ℝ) : intervalEnergy L 0 = 0 := by
  unfold intervalEnergy
  have h := energy_extend_congr_ae (L := L) (Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (-L) L)))
  simpa [extend, energy] using h

lemma zero_mem (L : ℝ) : InDomain L 0 := by
  unfold InDomain
  rw [intervalEnergy_zero]
  exact ENNReal.zero_lt_top

/-- Safe round trip is available only with an explicit finite-energy proof. -/
lemma finite_toReal (L : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : InDomain L f) : ENNReal.ofReal (intervalEnergy L f).toReal = intervalEnergy L f :=
  ENNReal.ofReal_toReal (ne_of_lt hf)
end RHFormDomain
