import RpErr0506
import GApprox0501

/-! # 0508: replacing `T` by `−log − Gq + g0` in `Tp`

`TpX n k = ∫_{−L}^{L} ½(−log(L−x) − log(L+x) − Gq(L−x) − Gq(L+x) + 2g0) b_n b_k`, `g0 = 2log2 + π/2`.
`|Tp n k − TpX n k| ≤ 2·10⁻²⁴ · L` (0501 `g_approx`, AM–GM `absprod_le`). -/

open MeasureTheory Set

namespace RHTpErr0508
open RHConditionalLog5 RHLog5Bridge RHGApprox0501

local notation "Lw" => halfWidth

noncomputable def g0 : ℝ := 2 * Real.log 2 + Real.pi / 2

noncomputable def TpX (n k : ℕ) : ℝ := ∫ x in (-Lw)..Lw,
  (1/2:ℝ) * (-Real.log (Lw - x) - Real.log (Lw + x) - Gq (Lw - x) - Gq (Lw + x) + 2 * g0) *
    (basisPoly n).eval x * (basisPoly k).eval x

lemma logm_ii : IntervalIntegrable (fun x => Real.log (Lw - x)) volume (-Lw) Lw := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 2 * Lw) (b := 0)).comp_sub_left Lw
  have e1 : Lw - 2 * Lw = -Lw := by ring
  rw [e1, sub_zero] at h; exact h

lemma logp_ii : IntervalIntegrable (fun x => Real.log (Lw + x)) volume (-Lw) Lw := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2 * Lw)).comp_add_left Lw
  have e1 : 2 * Lw - Lw = Lw := by ring
  rw [e1, zero_sub] at h; exact h

@[fun_prop] lemma Gq_cont' : Continuous Gq := continuous_Gq

lemma fX_ii (n k : ℕ) : IntervalIntegrable (fun x => (1/2:ℝ) * (-Real.log (Lw - x) - Real.log (Lw + x) -
    Gq (Lw - x) - Gq (Lw + x) + 2 * g0) * (basisPoly n).eval x * (basisPoly k).eval x) volume (-Lw) Lw := by
  have hb : Continuous fun x => (basisPoly n).eval x * (basisPoly k).eval x := by fun_prop
  have h1 := (logm_ii.mul_continuousOn hb.continuousOn)
  have h2 := (logp_ii.mul_continuousOn hb.continuousOn)
  have h3 : IntervalIntegrable (fun x => (-Gq (Lw - x) - Gq (Lw + x) + 2 * g0) *
      ((basisPoly n).eval x * (basisPoly k).eval x)) volume (-Lw) Lw :=
    (by fun_prop : Continuous fun x => (-Gq (Lw - x) - Gq (Lw + x) + 2 * g0) *
      ((basisPoly n).eval x * (basisPoly k).eval x)).intervalIntegrable _ _
  have h := ((h1.neg.sub h2).add h3).const_mul (1/2:ℝ)
  refine h.congr (fun x _ => ?_)
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

theorem Tp_err (n k : ℕ) : |RHColDecomp0499.Tp n k - TpX n k| ≤ 2 / 10 ^ 24 * Lw := by
  have hL := halfWidth_pos
  set ε : ℝ := 2 / 10 ^ 24 with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have eT : RHColDecomp0499.Tp n k = ∫ x in (-Lw)..Lw, (1/2:ℝ) * (RH_Rebaseline.T_tail (Lw - x) +
      RH_Rebaseline.T_tail (Lw + x)) * (basisPoly n).eval x * (basisPoly k).eval x := by
    unfold RHColDecomp0499.Tp; rw [RHEntry00_0495.setI]
  have hTi : IntervalIntegrable (fun x => (1/2:ℝ) * (RH_Rebaseline.T_tail (Lw - x) +
      RH_Rebaseline.T_tail (Lw + x)) * (basisPoly n).eval x * (basisPoly k).eval x) volume (-Lw) Lw := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact RHColDecomp0499.T_intOn n k
  rw [eT, TpX, ← intervalIntegral.integral_sub hTi (fX_ii n k)]
  have hbc : Continuous fun x => ε * Lw * (|(basisPoly n).eval x| * |(basisPoly k).eval x|) := by fun_prop
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ (hbc.intervalIntegrable _ _)).trans ?_
  swap
  · rw [intervalIntegral.integral_const_mul]
    have := RHRpErr0506.absprod_le n k
    calc _ ≤ ε * Lw * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε * Lw := by ring
  · filter_upwards [Measure.ae_ne volume Lw] with x hne hx
    have hx1 : 0 < Lw - x := by
      have : x < Lw := lt_of_le_of_ne hx.2 hne
      linarith
    have hx2 : 0 < Lw + x := by linarith [hx.1]
    have h5 : 2 * Lw = Real.log 5 := RHRpErr0506.twoL
    have e1 := g_approx hx1 (by linarith [hx.1])
    have e2 := g_approx hx2 (by linarith [hx.2])
    rw [Real.norm_eq_abs]
    have hid : (1/2:ℝ) * (RH_Rebaseline.T_tail (Lw - x) + RH_Rebaseline.T_tail (Lw + x)) *
        (basisPoly n).eval x * (basisPoly k).eval x -
        (1/2:ℝ) * (-Real.log (Lw - x) - Real.log (Lw + x) - Gq (Lw - x) - Gq (Lw + x) + 2 * g0) *
        (basisPoly n).eval x * (basisPoly k).eval x =
        (1/2:ℝ) * ((RH_Rebaseline.T_tail (Lw - x) + Real.log (Lw - x) + Gq (Lw - x) - (2 * Real.log 2 + Real.pi / 2)) +
          (RH_Rebaseline.T_tail (Lw + x) + Real.log (Lw + x) + Gq (Lw + x) - (2 * Real.log 2 + Real.pi / 2))) *
        ((basisPoly n).eval x * (basisPoly k).eval x) := by
      unfold g0; ring
    rw [hid, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hsum := abs_add_le (RH_Rebaseline.T_tail (Lw - x) + Real.log (Lw - x) + Gq (Lw - x) - (2 * Real.log 2 + Real.pi / 2))
      (RH_Rebaseline.T_tail (Lw + x) + Real.log (Lw + x) + Gq (Lw + x) - (2 * Real.log 2 + Real.pi / 2))
    have hb := mul_nonneg (abs_nonneg ((basisPoly n).eval x)) (abs_nonneg ((basisPoly k).eval x))
    have : (1/2:ℝ) * |(RH_Rebaseline.T_tail (Lw - x) + Real.log (Lw - x) + Gq (Lw - x) - (2 * Real.log 2 + Real.pi / 2)) +
          (RH_Rebaseline.T_tail (Lw + x) + Real.log (Lw + x) + Gq (Lw + x) - (2 * Real.log 2 + Real.pi / 2))| ≤ ε * Lw := by
      rw [hε]; nlinarith
    calc _ ≤ ε * Lw * (|(basisPoly n).eval x| * |(basisPoly k).eval x|) :=
          mul_le_mul_of_nonneg_right this hb
      _ = _ := rfl

end RHTpErr0508

