import SpatialPolarization0489
import SpatialDensity0490
import FinalIntegration0488

/-! # 0489: G2 without research inputs; fixed log 5 target conditional only on G5RawBound, G6RawBound
 -/

namespace RHG2Final0489
open RHConditionalLog5 RHConcreteParameters

theorem g2 : G2 concrete :=
  RHStepA2G2.g2_of_spatial_components RHSpatialPolarization0489.spatialEnergyPolarization
    RHSpatialDensity0490.spatialEnergyDensityIntegral

theorem target_log5_of_G5_G6
    (h5 : RHStepB3G5.G5RawBound) (h6 : RHStepB2G6.G6RawBound)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHFinalIntegration0488.target_log5_of_remaining_inputs
    RHSpatialPolarization0489.spatialEnergyPolarization
    RHSpatialDensity0490.spatialEnergyDensityIntegral h5 h6 f hf hs hn

end RHG2Final0489

