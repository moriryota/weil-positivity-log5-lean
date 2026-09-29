import TargetLog5Interface
import SpatialToTargetBridge
import SchurPositiveIntegration
import Mathlib.Data.Real.Basic

/-
# TargetLog5Integration.lean

Conditional formalization of milestone TARGET_LOG5:
"Strict positivity of the full Weil explicit quadratic form for all non-zero
complex C_c^2 test functions supported in [-log 5 / 2, log 5 / 2]."

This module:
1. Discharges `h_eq` from E_SPATIAL (`spatial_identity_of_test`) by defining the concrete
   spatial explicit formula form `targetQ` and proving `target_spatial_identity`.
2. Connects summability from D_TEST via `summable_of_test`.
3. Takes positivity `h_pos : f ≠ 0 → 0 < targetQ f` (S_POSITIVE) as a hypothesis; it is discharged in `RHCaps0494.target_log5_of_gaps_caps`.
-/

namespace RHTargetLog5

open Real MeasureTheory Set
open Zeta23
open RHLog5Bridge
open RHSpatialDomain
open RHComplexSpatialEndpoint
open RHComplexSpatial
open scoped ComplexConjugate
open RHTargetLog5Interface
open RHSpatialToTargetBridge
open RHSchurPositive

/-- The concrete full Weil explicit quadratic form in real-space representation.
This matches the exact right-hand side of `spatial_identity_of_test` from E_SPATIAL. -/
noncomputable def targetQ (f : ℝ → ℂ) : ℝ :=
  ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * (∫ x, ‖f x‖^2) +
  complexSpatialEnergy f +
  2 * ‖∫ x, f x * (Real.cosh (x / 2) : ℂ)‖^2 - 2 * ‖∫ x, f x * (Real.sinh (x / 2) : ℂ)‖^2 -
  2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (∫ t, f t * conj (f (t - Real.log n))).re

/-- Concrete spatial identity: Re W(f, f) = targetQ f holds unconditionally for all valid test functions.
Discharges h_eq from E_SPATIAL (`spatial_identity_of_test`). -/
theorem target_spatial_identity (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) :
    (zetaZeroConfig.W f f).re = targetQ f :=
  spatial_identity_of_test f hf hs

/-- Full endpoint theorem combining spatial explicit representation with quadratic positivity.
`h_eq` is completely discharged via `target_spatial_identity` (E_SPATIAL).
The only hypothesis besides the test-function conditions is `h_pos : f ≠ 0 → 0 < targetQ f` (S_POSITIVE). -/
theorem target_log5_endpoint
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) (hn : f ≠ 0)
    (h_pos : f ≠ 0 → 0 < targetQ f) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (zetaZeroConfig.W f f).re := by
  have hsum := summable_of_test f hf hs hn
  have heq := target_spatial_identity f hf hs
  have hQ_pos := h_pos hn
  rw [heq]
  exact ⟨hsum, hQ_pos⟩

/-- Support inclusion theorem: smaller supports inherit strict positivity without induction. -/
theorem target_log5_of_support_le
    (f : ℝ → ℂ) {L : ℝ} (hL : L ≤ halfWidth)
    (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) (hn : f ≠ 0)
    (h_pos : f ≠ 0 → 0 < targetQ f) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (zetaZeroConfig.W f f).re := by
  have hs_trans := support_le_trans hL hs
  exact target_log5_endpoint f hf hs_trans hn h_pos

end RHTargetLog5

