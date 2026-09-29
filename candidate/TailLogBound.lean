import RealAutocorr
import Mathlib.Analysis.Calculus.Deriv.MeanValue
open Set
namespace RHTailLogBound
open RH_Rebaseline
lemma kernel_le {A t : ℝ} (ht : 0 < t) (hA : t ≤ A) :
    K_kernel t ≤ Real.exp (A/2) / t := by
  unfold K_kernel
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
    (Real.sinh_pos_iff.mpr ht).le).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le ht (Real.self_le_sinh_iff.mpr ht.le))

theorem tail_log_bound {A b : ℝ} (hb : 0 < b) (hA : b ≤ A) :
    T_tail b ≤ T_tail A + Real.exp (A/2) * (Real.log A - Real.log b) := by
  let F : ℝ → ℝ := fun x => T_tail x + Real.exp (A/2) * Real.log x
  have hd (x : ℝ) (hx : x ∈ Icc b A) :
      HasDerivAt F (-K_kernel x + Real.exp (A/2) * x⁻¹) x := by
    exact (hasDerivAt_T_tail (hb.trans_le hx.1)).add
      ((Real.hasDerivAt_log (ne_of_gt (hb.trans_le hx.1))).const_mul _)
  have hm : MonotoneOn F (Icc b A) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b A)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    have hk := kernel_le (hb.trans_le hx'.1) hx'.2
    simpa only [div_eq_mul_inv, sub_eq_add_neg, add_comm] using sub_nonneg.mpr hk
  have h := hm (left_mem_Icc.mpr hA) (right_mem_Icc.mpr hA) hA
  dsimp [F] at h
  nlinarith

theorem right_tail_log_bound {L x : ℝ} (hx : |x| < L) :
    T_tail (L-x) ≤ T_tail (2*L) + Real.exp L * (Real.log (2*L)-Real.log (L-x)) := by
  have hh := abs_lt.mp hx
  have h := tail_log_bound (A := 2*L) (b := L-x) (by linarith) (by linarith)
  simpa only [mul_div_cancel_left₀ L (by norm_num : (2:ℝ) ≠ 0)] using h

theorem left_tail_log_bound {L x : ℝ} (hx : |x| < L) :
    T_tail (L+x) ≤ T_tail (2*L) + Real.exp L * (Real.log (2*L)-Real.log (L+x)) := by
  have hh := abs_lt.mp hx
  have h := tail_log_bound (A := 2*L) (b := L+x) (by linarith) (by linarith)
  simpa only [mul_div_cancel_left₀ L (by norm_num : (2:ℝ) ≠ 0)] using h
end RHTailLogBound
