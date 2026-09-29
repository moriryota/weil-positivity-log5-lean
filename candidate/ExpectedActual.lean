import ActualDirections
open MeasureTheory Set
namespace RHExpected0252

theorem direction_inner (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    inner ℂ (RHLegendreDirections.direction L hL.le m)
      (RHLegendreDirections.direction L hL.le n) = if m=n then 1 else 0 :=
  (orthonormal_iff_ite.mp (RHLegendreActual.directions_orthonormal hL)) m n

theorem projection_coefficients (L : ℝ) (hL : 0 < L)
    (s : Finset ℕ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    RHFiniteProjection.finiteProjection s (RHLegendreDirections.direction L hL.le) f =
      ∑ n ∈ s, inner ℂ (RHLegendreDirections.direction L hL.le n) f •
        RHLegendreDirections.direction L hL.le n :=
  RHLegendreActual.projection_eq_sum hL s f
end RHExpected0252
