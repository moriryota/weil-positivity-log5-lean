import RealBasisInterval
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory Set
open scoped ComplexConjugate
namespace RHRealCoefficientBridge
open RHConditionalLog5 RHLog5Bridge RHRealBasisBridge
noncomputable abbrev μ := volume.restrict (Icc (-halfWidth) halfWidth)
lemma coeff_interval (u : ℝ → ℝ) (n : ℕ) :
    (∫ x, basis n x * u x ∂μ) = coeff u n := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [basis, RHWeilColumnCandidate.zeroPoly, hx]
lemma inner_eq_coeff (u : ℝ → ℝ) (n : ℕ) (f : Lp ℂ 2 μ)
    (hf : (f : ℝ → ℂ) =ᵐ[μ] (fun x => (u x : ℂ))) :
    inner ℂ (RHLegendreDirections.direction halfWidth halfWidth_pos.le n) f =
      (coeff u n : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ((basis n x * u x : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [direction_eq_basis_ae n, hf] with x hx hy
      rw [hx, hy]
      simp [RCLike.inner_apply, mul_comm]
    _ = ((∫ x, basis n x * u x ∂μ : ℝ) : ℂ) := integral_complex_ofReal
    _ = (coeff u n : ℂ) := by rw [coeff_interval]
noncomputable def intervalEmbed (u : ℝ → ℝ) (hu : MemLp u 2 volume) : Lp ℂ 2 μ :=
  ((hu.restrict (Icc (-halfWidth) halfWidth)).ofReal).toLp (fun x => (u x : ℂ))
lemma inner_intervalEmbed (u : ℝ → ℝ) (hu : MemLp u 2 volume) (n : ℕ) :
    inner ℂ (RHLegendreDirections.direction halfWidth halfWidth_pos.le n) (intervalEmbed u hu) =
      (coeff u n : ℂ) :=
  inner_eq_coeff u n _ ((hu.restrict (Icc (-halfWidth) halfWidth)).ofReal.coeFn_toLp)
lemma norm_intervalEmbed (u : ℝ → ℝ) (hu : MemLp u 2 volume)
    (hs : ∀ x, x ∉ Icc (-halfWidth) halfWidth → u x = 0) :
    ‖intervalEmbed u hu‖ = ‖embed u‖ := by
  have hi : (Icc (-halfWidth) halfWidth).indicator u = u := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · simp [hx]
    · simp [hx, hs x hx]
  have hn : eLpNorm (fun x => (u x : ℂ)) 2 μ = eLpNorm u 2 μ := by
    apply eLpNorm_congr_norm_ae (hu.restrict (Icc (-halfWidth) halfWidth)).ofReal.aestronglyMeasurable
      (hu.restrict (Icc (-halfWidth) halfWidth)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simp)
  simp only [intervalEmbed, Lp.norm_toLp, embed, dif_pos hu]
  rw [hn, ← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc, hi]
end RHRealCoefficientBridge
