import FixedCoordinates
import ConditionalLog5
namespace RHFixedCoordinatesAdapter
open scoped Matrix
noncomputable def coordinates (o : Bool) (u : ℝ → ℝ) : Fin 32 → ℝ :=
  RHFixedCoordinates.coordinates o (RHConditionalLog5.alpha o u)
/-- The actual G3 coordinate identity. No Test or positivity premise is needed. -/
theorem alpha_identity (o : Bool) (u : ℝ → ℝ) :
    RHFixedCoordinates.B o *ᵥ coordinates o u = RHConditionalLog5.alpha o u :=
  RHFixedCoordinates.coordinates_identity o (RHConditionalLog5.alpha o u)
end RHFixedCoordinatesAdapter
