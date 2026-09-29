import TpErr0508
import TpA0508

/-! # 0508: `TpX` in Legendre form

With `P = p_n p_k = evV N (V n k)` (`N = n+k+1`), `G(w) = Gq(L w) = Σ_i gm_i w^i`:
`TpX n k = L c_n c_k · [ (g0 − log L)·∫P − ½(1 + (−1)^{n+k}) (Σ_l V_l μ_l + Σ_i gm_i Σ_l V_l·2/(2l+1)·β 0 i l) ]`.
 -/

open MeasureTheory Set Finset intervalIntegral
open scoped BigOperators Interval

namespace RHTpScale0508
open RHConditionalLog5 RHLog5Bridge RHGApprox0501 RHTpErr0508 RHLeg0503 RHLegVec0503 RHIter0505 RHProd0508
  RHTpA0508 RHRpExact0506

local notation "Lw" => halfWidth

@[fun_prop] lemma cont_p (n : ℕ) : Continuous fun x => p n x := continuous_p n

def Mg : ℕ := (RHGApprox0501.integL RHRkApprox0500.ql).length
noncomputable def gm (i : ℕ) : ℝ :=
  2 * (((RHGApprox0501.integL RHRkApprox0500.ql).getD i 0 : ℚ) : ℝ) * (Lw / 2) ^ i

lemma G_expand (w : ℝ) : Gq (Lw * w) = ∑ i ∈ range Mg, gm i * w ^ i := by
  unfold Gq Mg gm
  rw [ev_eq_sum, mul_sum]
  exact sum_congr rfl (fun i _ => by ring)

lemma log1m_ii : IntervalIntegrable (fun x : ℝ => Real.log (1 - x)) volume (-1) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 2) (b := 0)).comp_sub_left 1
  norm_num at h; exact h

noncomputable def S (n k : ℕ) : ℝ :=
  ∑ l ∈ range (n + k + 1), V n k l * muR l +
    ∑ i ∈ range Mg, gm i * ∑ l ∈ range (n + k + 1), V n k l * (2 / (2 * l + 1) * β 0 i l)

lemma P_neg (n k : ℕ) (u : ℝ) : p n (-u) * p k (-u) = (-1) ^ (n + k) * (p n u * p k u) := by
  rw [p_neg, p_neg, pow_add]; ring

lemma logP (n k : ℕ) : ∫ u in (-1:ℝ)..1, Real.log (1 + u) * (p n u * p k u) =
    ∑ l ∈ range (n + k + 1), V n k l * muR l := by
  rw [← logint]; congr 1; funext u; rw [RHProd0508.prod_eq]

lemma GP (n k : ℕ) : ∫ u in (-1:ℝ)..1, Gq (Lw * (1 + u)) * (p n u * p k u) =
    ∑ i ∈ range Mg, gm i * ∑ l ∈ range (n + k + 1), V n k l * (2 / (2 * l + 1) * β 0 i l) := by
  have e : (fun u => Gq (Lw * (1 + u)) * (p n u * p k u)) =
      fun u => ∑ i ∈ range Mg, gm i * ((1 + u) ^ i * evV (n + k + 1) (V n k) u) := by
    funext u; rw [G_expand, sum_mul, RHProd0508.prod_eq]; exact sum_congr rfl (fun i _ => by ring)
  rw [e, integral_finsetSum (f := fun i u => gm i * ((1 + u) ^ i * evV (n + k + 1) (V n k) u))
    (fun i _ => ((continuous_const.mul ((by fun_prop : Continuous fun u : ℝ => (1 + u) ^ i).mul
      (RHLegVec0503.continuous_evV _ _)))).intervalIntegrable _ _)]
  exact sum_congr rfl (fun i _ => by rw [intervalIntegral.integral_const_mul, powint])

lemma lin5 {f1 f2 f3 f4 f5 : ℝ → ℝ} (h1 : IntervalIntegrable f1 volume (-1) 1)
    (h2 : IntervalIntegrable f2 volume (-1) 1) (h3 : IntervalIntegrable f3 volume (-1) 1)
    (h4 : IntervalIntegrable f4 volume (-1) 1) (h5 : IntervalIntegrable f5 volume (-1) 1) (a : ℝ) :
    ∫ u in (-1:ℝ)..1, (a * f1 u - 1/2 * f2 u - 1/2 * f3 u - 1/2 * f4 u - 1/2 * f5 u) =
      a * (∫ u in (-1:ℝ)..1, f1 u) - 1/2 * (∫ u in (-1:ℝ)..1, f2 u) - 1/2 * (∫ u in (-1:ℝ)..1, f3 u) -
        1/2 * (∫ u in (-1:ℝ)..1, f4 u) - 1/2 * (∫ u in (-1:ℝ)..1, f5 u) := by
  have g1 := h1.const_mul a
  have g2 := h2.const_mul (1/2:ℝ)
  have g3 := h3.const_mul (1/2:ℝ)
  have g4 := h4.const_mul (1/2:ℝ)
  have g5 := h5.const_mul (1/2:ℝ)
  rw [intervalIntegral.integral_sub (f := fun u => a * f1 u - 1/2 * f2 u - 1/2 * f3 u - 1/2 * f4 u)
      (g := fun u => 1/2 * f5 u) (((g1.sub g2).sub g3).sub g4) g5,
    intervalIntegral.integral_sub (f := fun u => a * f1 u - 1/2 * f2 u - 1/2 * f3 u)
      (g := fun u => 1/2 * f4 u) ((g1.sub g2).sub g3) g4,
    intervalIntegral.integral_sub (f := fun u => a * f1 u - 1/2 * f2 u)
      (g := fun u => 1/2 * f3 u) (g1.sub g2) g3,
    intervalIntegral.integral_sub (f := fun u => a * f1 u) (g := fun u => 1/2 * f2 u) g1 g2]
  simp only [intervalIntegral.integral_const_mul]

theorem TpX_eq (n k : ℕ) :
    TpX n k = Lw * cc n * cc k * ((g0 - Real.log Lw) * (∫ u in (-1:ℝ)..1, p n u * p k u) -
      (1/2:ℝ) * (1 + (-1) ^ (n + k)) * S n k) := by
  have hL := halfWidth_pos
  set fX : ℝ → ℝ := fun x => (1/2:ℝ) * (-Real.log (Lw - x) - Real.log (Lw + x) - Gq (Lw - x) - Gq (Lw + x) +
    2 * g0) * (basisPoly n).eval x * (basisPoly k).eval x with hfX
  have hscale : TpX n k = Lw * ∫ u in (-1:ℝ)..1, fX (Lw * u) := by
    have h := intervalIntegral.integral_comp_mul_left fX hL.ne' (a := -1) (b := 1)
    rw [smul_eq_mul, mul_neg, mul_one] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]; rfl
  set P : ℝ → ℝ := fun u => p n u * p k u with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hpt : ∀ᵐ u ∂volume, u ∈ Ι (-1:ℝ) 1 → fX (Lw * u) =
      cc n * cc k * ((g0 - Real.log Lw) * P u - 1/2 * (Real.log (1 - u) * P u) - 1/2 * (Real.log (1 + u) * P u) -
        1/2 * (Gq (Lw * (1 - u)) * P u) - 1/2 * (Gq (Lw * (1 + u)) * P u)) := by
    filter_upwards [Measure.ae_ne volume 1] with u hne hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    have h1 : (1 - u) ≠ 0 := by intro h; exact hne (by linarith)
    have h2 : (1 + u) ≠ 0 := by intro h; linarith [hu.1]
    have e1 : Lw - Lw * u = Lw * (1 - u) := by ring
    have e2 : Lw + Lw * u = Lw * (1 + u) := by ring
    rw [hfX]; simp only
    rw [e1, e2, Real.log_mul hL.ne' h1, Real.log_mul hL.ne' h2, bscale, bscale, hP]
    ring
  rw [hscale, intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_const_mul]
  have i1 : IntervalIntegrable (fun u => (g0 - Real.log Lw) * P u) volume (-1) 1 :=
    (continuous_const.mul hPc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => Real.log (1 - u) * P u) volume (-1) 1 :=
    log1m_ii.mul_continuousOn hPc.continuousOn
  have i3 : IntervalIntegrable (fun u => Real.log (1 + u) * P u) volume (-1) 1 :=
    RHLogMoment0508.log1p_ii.mul_continuousOn hPc.continuousOn
  have i4 : IntervalIntegrable (fun u => Gq (Lw * (1 - u)) * P u) volume (-1) 1 :=
    ((by fun_prop : Continuous fun u => Gq (Lw * (1 - u))).mul hPc).intervalIntegrable _ _
  have i5 : IntervalIntegrable (fun u => Gq (Lw * (1 + u)) * P u) volume (-1) 1 :=
    ((by fun_prop : Continuous fun u => Gq (Lw * (1 + u))).mul hPc).intervalIntegrable _ _
  have hlin := lin5 (a := 1) (f1 := fun u => (g0 - Real.log Lw) * P u) i1 i2 i3 i4 i5
  simp only [one_mul] at hlin
  rw [hlin, intervalIntegral.integral_const_mul]
  -- reflections
  have r2 : ∫ u in (-1:ℝ)..1, Real.log (1 - u) * P u = (-1) ^ (n + k) * ∫ u in (-1:ℝ)..1, Real.log (1 + u) * P u := by
    rw [refl_int (f := Real.log) (g := P), ← intervalIntegral.integral_const_mul]
    congr 1; funext u; rw [hP]; simp only; rw [P_neg]; ring
  have r4 : ∫ u in (-1:ℝ)..1, Gq (Lw * (1 - u)) * P u =
      (-1) ^ (n + k) * ∫ u in (-1:ℝ)..1, Gq (Lw * (1 + u)) * P u := by
    rw [refl_int (f := fun w => Gq (Lw * w)) (g := P), ← intervalIntegral.integral_const_mul]
    congr 1; funext u; rw [hP]; simp only; rw [P_neg]; ring
  rw [r2, r4]
  have l3 : ∫ u in (-1:ℝ)..1, Real.log (1 + u) * P u = ∑ l ∈ range (n + k + 1), V n k l * muR l := logP n k
  have l5 : ∫ u in (-1:ℝ)..1, Gq (Lw * (1 + u)) * P u =
      ∑ i ∈ range Mg, gm i * ∑ l ∈ range (n + k + 1), V n k l * (2 / (2 * l + 1) * β 0 i l) := GP n k
  rw [l3, l5, show (∫ u in (-1:ℝ)..1, p n u * p k u) = ∫ u in (-1:ℝ)..1, P u from rfl]
  unfold S
  ring

end RHTpScale0508

