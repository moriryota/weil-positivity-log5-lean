import DirectShiftIntegration
import G1Adapter0484

/-! # 0488: fixed-width log 5 target with G1 supplied

`RHG1Adapter0484.g1` (0486, research-input-free) is passed to the existing final entry
`RHStepBAssembly.target_log5_of_system_a_and_raw_certificates`, with `G2` obtained from the
two spatial components. The only remaining research inputs are the four hypotheses below.
 -/

namespace RHFinalIntegration0488
open RHConditionalLog5 RHConcreteParameters

theorem target_log5_of_remaining_inputs
    (h1 : RHStepA2G2.SpatialEnergyPolarization) (h2 : RHStepA2G2.SpatialEnergyDensityIntegral)
    (h5 : RHStepB3G5.G5RawBound) (h6 : RHStepB2G6.G6RawBound)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHStepBAssembly.target_log5_of_system_a_and_raw_certificates
    RHG1Adapter0484.g1 (RHStepA2G2.g2_of_spatial_components h1 h2) h5 h6 f hf hs hn

/-- Same conclusion as 0459's entry once its `FixedShiftLowerBound` is supplied by 0486. -/
theorem fixed_shift_lower_bound : RHDirectShiftIntegration.FixedShiftLowerBound :=
  ⟨RHG1Adapter0484.even_shift, RHG1Adapter0484.odd_shift⟩

theorem target_log5_via_0459
    (h1 : RHStepA2G2.SpatialEnergyPolarization) (h2 : RHStepA2G2.SpatialEnergyDensityIntegral)
    (h5 : RHStepB3G5.G5RawBound) (h6 : RHStepB2G6.G6RawBound)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHDirectShiftIntegration.target_log5_of_fixed_shift_and_spatial_components
    fixed_shift_lower_bound h1 h2 h5 h6 f hf hs hn

end RHFinalIntegration0488

