import TargetLog5Interface
import SpatialDomain
import ComplexSpatialEndpoint
import SchurPositiveIntegration
import Mathlib.Data.Real.Basic

/-
# SpatialToTargetBridge.lean

Bridge connecting the spatial domain representation from D_TEST and E_SPATIAL
to strict positivity of the explicit formula form.
-/

namespace RHSpatialToTargetBridge

open Real MeasureTheory Set
open Zeta23
open RHLog5Bridge
open RHSpatialDomain
open RHComplexSpatialEndpoint
open RHComplexSpatial
open scoped ComplexConjugate
open RHTargetLog5Interface
open RHSchurPositive

/-- Full zero summability from SpatialDomain for any valid log 5 test function. -/
theorem summable_of_test (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) (hn : f ≠ 0) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) := by
  have h := full_zero_domain f hf hs hn
  rcases h with ⟨g, _, _, _, hsum, _⟩
  exact hsum

/-- Spatial explicit identity holds for the real part of W(f, f). -/
theorem spatial_identity_of_test (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ halfWidth) :
    (zetaZeroConfig.W f f).re =
      ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi)*(∫ x, ‖f x‖^2) +
      complexSpatialEnergy f +
      2*‖∫ x, f x*(Real.cosh (x/2):ℂ)‖^2-2*‖∫ x, f x*(Real.sinh (x/2):ℂ)‖^2 -
      2*∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
        (∫ t, f t*conj (f (t-Real.log n))).re :=
  (full_zero_log5 f hf hs).2

end RHSpatialToTargetBridge

