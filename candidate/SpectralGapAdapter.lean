import BandNorm
import G3LowZeroAdapter
import ConcreteParameters
open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix
namespace RHSpectralGapAdapter
open RHConditionalLog5 RHG3BandConnection RHConcreteParameters
/-- Only the finite energy coefficient bound and sector Parseval remain for G3. -/
def SpectralInputs : Prop := ∀ o u, Test u →
  (∀ M, ∑ n ∈ Finset.range M, (harmonic (degree o n) : ℝ) * massCoeff o u n ≤ compare (tail o u)) ∧
  Tendsto (fun M => ∑ n ∈ Finset.range M, massCoeff o u n) atTop (𝓝 (‖embed (tail o u)‖^2))
theorem g3_of_spectral (h : SpectralInputs) : G3 concrete := by
  apply RHG3LowZeroAdapter.g3_of_remaining
  intro o u hu
  exact ⟨RHConcreteParameters.coordinates_identity o u, RHBandNorm.band_far_norm o u hu,
    (h o u hu).1, (h o u hu).2⟩
theorem target_log5_of_remaining
    (h1 : G1 concrete) (h2 : G2 concrete) (hspec : SpectralInputs)
    (h5 : G5 concrete) (h6 : G6 concrete)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHConcreteParameters.target_log5_of_remaining h1 h2 (g3_of_spectral hspec) h5 h6 f hf hs hn
end RHSpectralGapAdapter
