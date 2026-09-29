import RHSpatialBase0489

/-! # 0489 h1: `RHStepA2G2.SpatialEnergyPolarization` without research hypotheses
 -/

namespace RHSpatialPolarization0489
open RHConditionalLog5 RHSpatialBase0489

theorem spatialEnergyPolarization : RHStepA2G2.SpatialEnergyPolarization := by
  intro o u hu
  exact polarize_spatialEnergy (low_measurable o u) (tail_measurable o u hu)
    (low_energy_finite o u) (RHG1Energy.tail_energy_finite o u hu)

end RHSpatialPolarization0489

