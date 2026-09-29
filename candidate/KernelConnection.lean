import KernelJensen
import KernelElementary
import ComparisonTail
open MeasureTheory Set
namespace RHKernelConnection

theorem kernel_lower {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) :
    s⁻¹ ≤ Real.exp (s/2) / Real.sinh s :=
  RHKernelElementary.kernel_of_ratio hs (RHKernelJensen.sinh_ratio_bound hs hs2)

theorem kernel_le_original {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1) :
    ∀ x ∈ Icc (-L) L, ∀ y ∈ Icc (-L) L,
      RHComparisonEnergy.kernel (x-y) ≤ RHFormDomain.kernel (x-y) := by
  intro x hx y hy
  unfold RHComparisonEnergy.kernel RHFormDomain.kernel
  apply ENNReal.ofReal_le_ofReal
  by_cases hxy : x = y
  · simp [hxy]
  · have hs : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hs2 : |x-y| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
    exact kernel_lower hs hs2

theorem domain_of_original {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (hf : RHFormDomain.InDomain L f) :
    RHComparisonEnergy.InDomain L f :=
  RHComparisonEnergy.domain_of_original f hf (kernel_le_original hL hL1)

theorem log5_original_comparison_tail
    (f : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))))
    (hf : RHFormDomain.InDomain (Real.log 5/2) f) (N : ℕ) :
    (harmonic N : ℝ) * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (RHLegendreDirections.direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le) f‖ ^ 2 ≤
    (RHComparisonEnergy.intervalEnergy (Real.log 5/2)
      (f - RHFiniteProjection.finiteProjection (Finset.range N)
        (RHLegendreDirections.direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le) f)).toReal :=
  RHComparisonTail.log5_comparison_tail f
    (domain_of_original RHLog5Bridge.halfWidth_pos RHKernelElementary.log5_half_le_one f hf) N
end RHKernelConnection
