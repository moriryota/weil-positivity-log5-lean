import TestRecPoly
import TestConjunct2
import TestConjunct1
import SpectralGapAdapter

set_option maxRecDepth 200000

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix Polynomial
namespace RHSpectralInputs
open RHConditionalLog5 RHLog5Bridge RHResidualMembership RHRealLowZero RHTestRecPoly
open RHSpectralGapAdapter RHActualTail RHG3BandConnection RHRealCoefficientBridge
open RHComparisonEnergy RHComparisonIntegral RHKernelConnection RHTestRestriction
open RHRealBasisBridge RHTestConjunct2 RHTestConjunct1

/-- Unconditional discharge of both SpectralInputs conjuncts:
1. Finite harmonic-weighted coefficient energy bound
2. Sector Parseval L^2 norm convergence -/
theorem spectral_inputs_unconditional : SpectralInputs := by
  intro o u hu
  exact ⟨harmonic_massCoeff_le_compare o u hu, massCoeff_tendsto o u hu⟩

/-- G3 is completely unconditional for concrete parameters. -/
theorem g3_unconditional : G3 RHConcreteParameters.concrete :=
  g3_of_spectral spectral_inputs_unconditional

/-- Log-5 target theorem reduces to G1, G2, G5, G6 only, with G3 completely discharged. -/
theorem target_log5_unconditional_of_remaining
    (h1 : G1 RHConcreteParameters.concrete) (h2 : G2 RHConcreteParameters.concrete)
    (h5 : G5 RHConcreteParameters.concrete) (h6 : G6 RHConcreteParameters.concrete)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  target_log5_of_remaining h1 h2 spectral_inputs_unconditional h5 h6 f hf hs hn

end RHSpectralInputs

