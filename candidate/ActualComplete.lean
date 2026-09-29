import DenseConnection
import DirectionSpan
import ActualDirections
import Mathlib.Analysis.InnerProductSpace.l2Space
open MeasureTheory Set Filter
open scoped Topology
namespace RHActualComplete
open RHLegendreDirections

theorem direction_complete {L : ℝ} (hL : 0 < L) :
    (Submodule.span ℂ (Set.range (direction L hL.le))).topologicalClosure = ⊤ :=
  RHDenseConnection.direction_complete_of_span hL.le (RHDirectionSpan.span_directionPoly hL)

noncomputable def basis {L : ℝ} (hL : 0 < L) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Icc (-L) L))) :=
  HilbertBasis.mk (RHLegendreActual.directions_orthonormal hL)
    (le_of_eq (direction_complete hL).symm)

@[simp] lemma coe_basis {L : ℝ} (hL : 0 < L) :
    (basis hL : ℕ → Lp ℂ 2 (volume.restrict (Icc (-L) L))) = direction L hL.le := by
  unfold basis
  exact HilbertBasis.coe_mk _ _

theorem expansion {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    HasSum (fun n => inner ℂ (direction L hL.le n) f • direction L hL.le n) f := by
  simpa only [HilbertBasis.repr_apply_apply, coe_basis] using (basis hL).hasSum_repr f

theorem projection_tendsto {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    Tendsto (fun N => RHFiniteProjection.finiteProjection (Finset.range N)
      (direction L hL.le) f) atTop (𝓝 f) := by
  simpa only [RHLegendreActual.projection_eq_sum hL] using (expansion hL f).tendsto_sum_nat
end RHActualComplete
