import StepA1_G1
import StepA2_G2
import StepB_Assembly

namespace RHDirectShiftIntegration
open RHConditionalLog5 RHConcreteParameters RHWeilShift
open RHStepA1G1 RHStepA2G2 RHStepB2G6 RHStepB3G5

/-- The shift inequalities `q_o ≤ C_o` as a hypothesis structure; they are proved in `RHG1Adapter0484` (`even_shift`, `odd_shift`). -/
structure FixedShiftLowerBound : Prop where
  even : concrete.shift false ≤ c_even
  odd : concrete.shift true ≤ c_odd

theorem g1_of_fixed_shift (h : FixedShiftLowerBound) : G1 concrete :=
  g1_of_discharged h.even h.odd
    (tail_archimedean_bound false) (tail_archimedean_bound true)
    (tail_prime_bound_unconditional false) (tail_prime_bound_unconditional true)

/-- Conditional integration only. All five research inputs remain explicit. -/
theorem target_log5_of_fixed_shift_and_spatial_components
    (hshift : FixedShiftLowerBound)
    (h1 : SpatialEnergyPolarization) (h2 : SpatialEnergyDensityIntegral)
    (h5 : G5RawBound) (h6 : G6RawBound)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHStepBAssembly.target_log5_of_system_a_and_raw_certificates
    (g1_of_fixed_shift hshift) (g2_of_spatial_components h1 h2) h5 h6 f hf hs hn
end RHDirectShiftIntegration
