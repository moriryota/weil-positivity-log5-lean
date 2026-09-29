import PolynomialDensity
import PolynomialLpMap
open MeasureTheory Set
namespace RHDenseConnection
open RHBoundedWindow RHLegendreDirections RHPolynomialLpMap

/-- This wrapper exposes the remaining algebraic input instead of assuming completeness. -/
theorem direction_complete_of_span {L : ℝ} (hL : 0 ≤ L)
    (hspan : Submodule.span ℂ (Set.range (directionPoly L)) = ⊤) :
    (Submodule.span ℂ (Set.range (direction L hL))).topologicalClosure = ⊤ := by
  have he : Submodule.map (toLp L hL) (Submodule.span ℂ (Set.range (directionPoly L))) =
      Submodule.span ℂ (Set.range (direction L hL)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hspan, Submodule.map_top] at he
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  rw [← he]
  exact RHPolynomialDensity.intervalPolynomial_denseRange hL
end RHDenseConnection
