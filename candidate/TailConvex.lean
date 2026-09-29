import KernelMonotone
import Mathlib.Analysis.Convex.Deriv
open MeasureTheory Set
namespace RHExternalPotential
open RH_Rebaseline

theorem tail_convex : ConvexOn ℝ (Ioi 0) T_tail := by
  have hc : ContinuousOn T_tail (Ioi 0) :=
    fun x hx => (hasDerivAt_T_tail hx).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ T_tail (interior (Ioi 0)) := by
    intro x hx
    have hp : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    exact (hasDerivAt_T_tail hp).differentiableAt.differentiableWithinAt
  have hm : MonotoneOn (deriv T_tail) (interior (Ioi 0)) := by
    intro x hx y hy hxy
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    have hy' : 0 < y := by simpa only [interior_Ioi, mem_Ioi] using hy
    rw [(hasDerivAt_T_tail hx').deriv, (hasDerivAt_T_tail hy').deriv]
    exact neg_le_neg (kernel_antitone hx' hy' hxy)
  exact MonotoneOn.convexOn_of_deriv (convex_Ioi 0) hc hd hm

theorem tail_symmetric_lower {L x : ℝ} (hx : |x| < L) :
    T_tail L ≤ (T_tail (L-x) + T_tail (L+x)) / 2 := by
  have hx' := abs_lt.mp hx
  have ha : (0:ℝ) < L-x := by linarith
  have hb : (0:ℝ) < L+x := by linarith
  have h : T_tail ((1/2:ℝ) • (L-x) + (1/2:ℝ) • (L+x)) ≤
      (1/2:ℝ) • T_tail (L-x) + (1/2:ℝ) • T_tail (L+x) :=
    tail_convex.2 ha hb (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1/2:ℝ)*(L-x)+(1/2:ℝ)*(L+x) = L := by ring
  rw [he] at h
  linarith

theorem actual_tail_integral {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (t/2) / Real.sinh t) (Ioi b) ∧
    (∫ t in Ioi b, Real.exp (t/2) / Real.sinh t) = T_tail b :=
  ⟨integrableOn_Ioi_K_kernel hb, integral_Ioi_K_kernel_eq_T_tail hb⟩

theorem symmetric_integral_lower {L x : ℝ} (hx : |x| < L) :
    T_tail L ≤ (1/2:ℝ) *
      ((∫ t in Ioi (L-x), Real.exp (t/2) / Real.sinh t) +
       (∫ t in Ioi (L+x), Real.exp (t/2) / Real.sinh t)) := by
  have ha : 0 < L-x := by linarith [(abs_lt.mp hx).2]
  have hb : 0 < L+x := by linarith [(abs_lt.mp hx).1]
  rw [(actual_tail_integral ha).2, (actual_tail_integral hb).2]
  have h := tail_symmetric_lower hx
  linarith
theorem ae_symmetric_lower (L : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Icc (-L) L)),
      T_tail L ≤ (T_tail (L-x) + T_tail (L+x)) / 2 := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo (-L) L =ᵐ[volume] Icc (-L) L)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact tail_symmetric_lower (abs_lt.mpr hx)
end RHExternalPotential

