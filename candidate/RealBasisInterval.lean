import RealBasisBridge
open MeasureTheory Set
namespace RHRealBasisBridge
open RHConditionalLog5 RHLog5Bridge
lemma basis_complex (n : ℕ) (x : ℝ) :
    (basis n x : ℂ) =
      (Icc (-halfWidth) halfWidth).indicator
        (fun y : ℝ => (RHLegendreDirections.directionPoly halfWidth n).eval (y : ℂ)) x := by
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · simp only [basis, RHWeilColumnCandidate.zeroPoly, Set.indicator_of_mem hx]
    exact basisPoly_eval n x
  · simp [basis, RHWeilColumnCandidate.zeroPoly, hx]
lemma direction_eq_basis_ae (n : ℕ) :
    (RHLegendreDirections.direction halfWidth halfWidth_pos.le n : ℝ → ℂ) =ᵐ[
      volume.restrict (Icc (-halfWidth) halfWidth)] (fun x => (basis n x : ℂ)) := by
  filter_upwards [RHLegendreDirections.direction_coe_ae halfWidth_pos.le n,
    ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [basis_complex, Set.indicator_of_mem hmem]
  simpa only [RHLegendreDirections.directionPoly_eval] using hx
end RHRealBasisBridge
