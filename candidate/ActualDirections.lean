import FullRecurrence
import UnitGram
import ConditionalConnection
open MeasureTheory Set
namespace RHLegendreActual

theorem directions_orthonormal {L : ℝ} (hL : 0 < L) :
    Orthonormal ℂ (RHLegendreDirections.direction L hL.le) :=
  RHLegendreContract.directions_orthonormal_of_unit_data
    RHLegendreContract.Q_recurrence RHLegendreContract.Q_unit_gram hL

theorem projection_eq_sum {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    RHFiniteProjection.finiteProjection s (RHLegendreDirections.direction L hL.le) f =
      ∑ n ∈ s, inner ℂ (RHLegendreDirections.direction L hL.le n) f •
        RHLegendreDirections.direction L hL.le n :=
  RHLegendreContract.direction_projection_eq_sum_of_unit_data
    RHLegendreContract.Q_recurrence RHLegendreContract.Q_unit_gram hL s f
end RHLegendreActual
