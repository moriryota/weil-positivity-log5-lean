import FixedWeights
import FixedCoordinatesAdapter
namespace RHConcreteParameters
open RHConditionalLog5
open scoped Matrix BigOperators
noncomputable def concrete : Parameters where
  B := RHFixedCoordinates.B
  coordinates := RHFixedCoordinatesAdapter.coordinates
  shift := RHFixedWeights.shift
  weights := fun o i => (harmonic (degree o (32+i)) : ℝ) + RHFixedWeights.shift o

theorem coordinates_identity (o : Bool) (u : ℝ → ℝ) :
    concrete.B o *ᵥ concrete.coordinates o u = alpha o u :=
  RHFixedCoordinatesAdapter.alpha_identity o u

theorem g4 : G4 concrete := by
  intro o
  have hn : dN o ≤ (harmonic 64 : ℝ) + concrete.shift o := by
    simpa [dN, RHFixedWeights.lowerN, RHCertificateData.d64_even_lower,
      RHCertificateData.d64_odd_lower, concrete] using RHFixedWeights.lowerN_le o
  have hm : dM o ≤ (harmonic 128 : ℝ) + concrete.shift o := by
    simpa [dM, RHFixedWeights.lowerM, RHCertificateData.d128_even_lower,
      RHCertificateData.d128_odd_lower, concrete] using RHFixedWeights.lowerM_le o
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change dN o ≤ (harmonic (degree o (32+i)) : ℝ) + concrete.shift o
    have hi : 64 ≤ degree o (32+i) := by
      unfold degree; split <;> omega
    have hh : (harmonic 64 : ℝ) ≤ (harmonic (degree o (32+i)) : ℝ) := RHFixedWeights.harmonic_mono hi
    linarith
  · intro i
    exact le_rfl
  · have hi : 128 ≤ degree o 64 := by
      unfold degree; split <;> omega
    have hh : (harmonic 128 : ℝ) ≤ (harmonic (degree o 64) : ℝ) := RHFixedWeights.harmonic_mono hi
    linarith

/-- G4 is supplied for the fixed certificate parameters. Other gaps remain explicit. -/
theorem target_log5_of_remaining
    (h1 : G1 concrete) (h2 : G2 concrete) (h3 : G3 concrete)
    (h5 : G5 concrete) (h6 : G6 concrete)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHConditionalLog5.target_log5_of_gaps concrete h1 h2 h3 g4 h5 h6 f hf hs hn
end RHConcreteParameters
