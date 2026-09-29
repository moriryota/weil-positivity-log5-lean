import ActualComplete
open MeasureTheory Set
namespace RHActualTail
open RHLegendreDirections

theorem residual_coefficient_zero {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (N n : ℕ) (hn : n < N) :
    inner ℂ (direction L hL.le n)
      (f - RHFiniteProjection.finiteProjection (Finset.range N)
        (direction L hL.le) f) = 0 := by
  rw [inner_sub_right, RHLegendreActual.projection_eq_sum hL]
  rw [(RHLegendreActual.directions_orthonormal hL).inner_right_sum
    (fun i => inner ℂ (direction L hL.le i) f) (Finset.mem_range.mpr hn)]
  exact sub_self _
end RHActualTail
