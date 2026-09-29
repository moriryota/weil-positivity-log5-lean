import ActualCorrelation
open MeasureTheory Set
namespace RHActualCorrelation

theorem zero_extension_overlap_integral (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (d : ℝ) (hd : 0≤d) :
    (∫ x in Ico (-L) (L-d), (Icc (-L) L).indicator (f : ℝ → ℝ) x *
      (Icc (-L) L).indicator (f : ℝ → ℝ) (x+d)) = autocorr L f d := by
  have hi := RHShiftOverlap.overlap_integral ((Icc (-L) L).indicator (f : ℝ → ℝ)) (-L) L d hd
  have hu : (Icc (-L) L).indicator ((Icc (-L) L).indicator (f : ℝ → ℝ)) =
      (Icc (-L) L).indicator (f : ℝ → ℝ) := by
    funext x
    by_cases hx : x ∈ Icc (-L) L <;> simp [hx]
  rw [hu] at hi
  exact hi.symm
end RHActualCorrelation
