import TargetLog5Interface
import TargetLog5Integration
import SpatialDomain
import RealSpatialEndpoint
import ComplexSpatialEndpoint
import ComplexSpatialParts
import ComplexEnergy
import ComplexSplit
import Mathlib.Data.Real.Basic

/-
# TargetFormBinding.lean

Formalization of milestone S_BIND:
"Decomposition of the concrete Weil form targetQ f into real and imaginary components,
and identification of the concrete target form with the Lp form domain energy."

This module establishes:
1. `targetQ_real (u : ℝ → ℝ)`: The real-valued explicit quadratic form.
2. `targetQ_split`: Unconditional theorem proving that `targetQ f` splits into
   `targetQ_real (Re f) + targetQ_real (Im f)` for all valid test functions.
3. `targetQ_lp_energy`: Identification of `complexSpatialEnergy f` in `targetQ f`
   with the true Lp form-domain intervalEnergy `(intervalEnergy (log 5 / 2) g).toReal`.
4. `targetQ_pos_of_real_pos`: Exact reduction of full complex test-function positivity
   to real test-function positivity.
-/

namespace RHTargetFormBinding

open Real MeasureTheory Set
open Zeta23
open RH_LiteratureBridge
open RHLog5Bridge
open RHFormDomain
open RHSpatialDomain
open RHComplexSpatialEndpoint
open RHComplexSpatial
open RHComplexFrequency
open RHAutocorrEnergy
open scoped ComplexConjugate
open RHTargetLog5Interface
open RHTargetLog5
open RHTestRestriction

/-- The concrete Weil explicit quadratic form for real-valued test functions. -/
noncomputable def targetQ_real (u : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * (∫ x, (u x)^2) +
  spatialEnergy u +
  2 * (∫ x, u x * Real.cosh (x / 2))^2 - 2 * (∫ x, u x * Real.sinh (x / 2))^2 -
  2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    real_autocorr u (Real.log n)

/-- Unconditional decomposition theorem: `targetQ f` splits into the sum of `targetQ_real`
evaluated on the real and imaginary parts of f. -/
theorem targetQ_split (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) :
    targetQ f = targetQ_real (fun x => (f x).re) + targetQ_real (fun x => (f x).im) := by
  have hL := halfWidth_pos
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hc := compact_of_support hs
  unfold targetQ targetQ_real
  rw [integral_norm_sq_parts hf.continuous hc]
  rw [complex_spatial_parts hL hf1 hs]
  rw [norm_integral_weight_parts hf.continuous hc (fun x => Real.cosh (x/2)) (by fun_prop)]
  rw [norm_integral_weight_parts hf.continuous hc (fun x => Real.sinh (x/2)) (by fun_prop)]
  have hsum : (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (∫ t, f t * conj (f (t - Real.log n))).re) =
      (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        real_autocorr (fun x => (f x).re) (Real.log n)) +
      (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        real_autocorr (fun x => (f x).im) (Real.log n)) := by
    simp_rw [autocorr_re_parts hf.continuous hc, mul_add]
    exact Finset.sum_add_distrib
  rw [hsum]
  ring

/-- Form domain identification: `targetQ f` coincides with the expression containing
the concrete Lp form domain intervalEnergy for g = testLp f. -/
theorem targetQ_lp_energy (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    ∃ g : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5 / 2)) (Real.log 5 / 2))),
      InDomain (Real.log 5 / 2) g ∧ g = testLp hf.continuous (Real.log 5 / 2) ∧ g ≠ 0 ∧
      targetQ f =
        ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * (∫ x, ‖f x‖^2) +
        (intervalEnergy (Real.log 5 / 2) g).toReal +
        2 * ‖∫ x, f x * (Real.cosh (x/2):ℂ)‖^2 - 2 * ‖∫ x, f x * (Real.sinh (x/2):ℂ)‖^2 -
        2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          (∫ t, f t * conj (f (t - Real.log n))).re := by
  have hdom := full_zero_domain f hf hs hn
  rcases hdom with ⟨g, hin, hg_eq, hgne, _, hW_eq⟩
  have h_eq := target_spatial_identity f hf hs
  refine ⟨g, hin, hg_eq, hgne, ?_⟩
  rw [← h_eq, hW_eq]

/-- Positivity reduction: if `targetQ_real` is strictly positive on all non-zero real test functions
and non-negative on all real test functions, then `targetQ f > 0` for all non-zero complex test functions. -/
theorem targetQ_pos_of_real_pos (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) (hn : f ≠ 0)
    (h_pos_re : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → u ≠ 0 → 0 < targetQ_real u)
    (h_nonneg_re : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u x ≠ 0 → |x| ≤ halfWidth) → 0 ≤ targetQ_real u) :
    0 < targetQ f := by
  rw [targetQ_split f hf hs]
  have hne := re_ne_zero_or_im_ne_zero hn
  have hrd : ContDiff ℝ 2 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hid : ContDiff ℝ 2 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hrs : ∀ x, (f x).re ≠ 0 → |x| ≤ halfWidth := re_support hs
  have his : ∀ x, (f x).im ≠ 0 → |x| ≤ halfWidth := im_support hs
  rcases hne with h_re_ne | h_im_ne
  · have h1 := h_pos_re (fun x => (f x).re) hrd hrs h_re_ne
    have h2 := h_nonneg_re (fun x => (f x).im) hid his
    exact add_pos_of_pos_of_nonneg h1 h2
  · have h1 := h_nonneg_re (fun x => (f x).re) hrd hrs
    have h2 := h_pos_re (fun x => (f x).im) hid his h_im_ne
    exact add_pos_of_nonneg_of_pos h1 h2

end RHTargetFormBinding

