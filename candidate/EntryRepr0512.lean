import RpEncl0506
import TpEncl0509

/-! # 0512: additive representations of Rp and Tp with uniform error bounds

For `n, k ≤ 127`:
* `Rp n k = F_R · γ n 81 (rval rq) k + E`, `|E| ≤ 4·10⁻²⁴`, `F_R = L² c_n c_k/(2k+1)`;
* `Tp n k = [n=k]·Cd − L c_n c_k σ · TS n 82 gq k (n+k+1) + E`, `|E| ≤ 2·10⁻²⁴`.
 -/

open Finset
open scoped BigOperators

namespace RHEntryRepr0512
open RHConditionalLog5 RHLog5Bridge RHLeg0503 RHRpExact0506 RHAlgoBall0505 RHGForm0505 RHTpScale0508 RHTpBall0509 RHTpEncl0509
  RHTpErr0508 RHProd0508 RHIter0505 RHTpA0508

lemma L_le : halfWidth ≤ 81 / 100 := by
  have h5 := RHEntry00Bounds0495.b_l5.2
  have : (RHEntry00Bounds0495.l5H : ℝ) ≤ 162 / 100 := by
    have : RHEntry00Bounds0495.l5H ≤ 162 / 100 := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr this; push_cast at h; exact h
  unfold halfWidth; linarith

lemma L_ge : 80 / 100 ≤ halfWidth := by
  have h5 := RHEntry00Bounds0495.b_l5.1
  have : (160 / 100 : ℝ) ≤ (RHEntry00Bounds0495.l5L : ℝ) := by
    have : (160 / 100 : ℚ) ≤ RHEntry00Bounds0495.l5L := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr this; push_cast at h; exact h
  unfold halfWidth; linarith

lemma cc_sq (n : ℕ) : cc n * cc n = (2 * n + 1) / (2 * halfWidth) :=
  Real.mul_self_sqrt (by have := halfWidth_pos; positivity)

lemma cc_nonneg (n : ℕ) : 0 ≤ cc n := Real.sqrt_nonneg _

/-- `L c_n c_k ≤ 128` for `n, k ≤ 127`. -/
lemma Lcc_le {n k : ℕ} (hn : n ≤ 127) (hk : k ≤ 127) : halfWidth * cc n * cc k ≤ 128 := by
  have hL := halfWidth_pos
  have h1 : cc n * cc k ≤ (cc n * cc n + cc k * cc k) / 2 := by nlinarith [sq_nonneg (cc n - cc k)]
  rw [cc_sq, cc_sq] at h1
  have hn' : (n : ℝ) ≤ 127 := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ 127 := by exact_mod_cast hk
  have : halfWidth * (cc n * cc k) ≤ halfWidth * (((2 * n + 1) / (2 * halfWidth) + (2 * k + 1) / (2 * halfWidth)) / 2) :=
    mul_le_mul_of_nonneg_left h1 hL.le
  have e : halfWidth * (((2 * (n : ℝ) + 1) / (2 * halfWidth) + (2 * k + 1) / (2 * halfWidth)) / 2) = ((2 * n + 1) + (2 * k + 1)) / 4 := by
    field_simp; ring
  rw [e] at this
  nlinarith

theorem Rp_repr {n k : ℕ} (hn : n ≤ 127) (hk : k ≤ 127) :
    ∃ E : ℝ, |E| ≤ 4 / 10 ^ 24 ∧
      RHColDecomp0499.Rp n k = halfWidth ^ 2 * cc n * cc k / (2 * k + 1) * γ n 81 (rval RHEntry22_0505.rq) k + E := by
  have hL := halfWidth_pos
  have hQ := RpQ_eq n k
  rw [RHRpCoef0506.J_eq] at hQ
  have hc := RHRpCoef0506.coef_err n k
  rw [RHRpCoef0506.J_eq] at hc
  have he := RHRpErr0506.Rp_err n k
  set F := halfWidth ^ 2 * cc n * cc k / (2 * k + 1) with hF
  refine ⟨RHColDecomp0499.Rp n k - F * γ n 81 (rval RHEntry22_0505.rq) k, ?_, by ring⟩
  have hk1 : (1:ℝ) ≤ 2 * k + 1 := by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
  have hF0 : 0 ≤ F := by rw [hF]; exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (cc_nonneg n)) (cc_nonneg k)) (by linarith)
  have hFle : F ≤ 104 := by
    have h := Lcc_le hn hk
    have hLc : 0 ≤ halfWidth * cc n * cc k := mul_nonneg (mul_nonneg hL.le (cc_nonneg n)) (cc_nonneg k)
    have e : F = halfWidth * (halfWidth * cc n * cc k) / (2 * k + 1) := by rw [hF]; ring
    have h1 : F ≤ halfWidth * (halfWidth * cc n * cc k) := by
      rw [e]; exact div_le_self (mul_nonneg hL.le hLc) hk1
    have h2 : halfWidth * (halfWidth * cc n * cc k) ≤ 81 / 100 * 128 := mul_le_mul L_le h hLc (by norm_num)
    linarith
  have hk' : (k : ℝ) ≤ 127 := by exact_mod_cast hk
  have e1 : |F * (γ n 81 rt k - γ n 81 (rval RHEntry22_0505.rq) k)| ≤ 104 * (4 * 255 / 10 ^ 32) := by
    rw [abs_mul, abs_of_nonneg hF0]
    have : |γ n 81 rt k - γ n 81 (rval RHEntry22_0505.rq) k| ≤ 4 * 255 / 10 ^ 32 := by
      refine hc.trans ?_; apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    exact mul_le_mul hFle this (abs_nonneg _) (by norm_num)
  have e2 : 2 / 10 ^ 24 / 2 * (2 * halfWidth + ((1 + 2 * halfWidth) / 2) ^ 2) ≤ 34 / 10 ^ 25 := by
    have := L_le; have := hL; nlinarith
  have hid : RHColDecomp0499.Rp n k - F * γ n 81 (rval RHEntry22_0505.rq) k =
      (RHColDecomp0499.Rp n k - RpQ n k) + F * (γ n 81 rt k - γ n 81 (rval RHEntry22_0505.rq) k) := by
    rw [hQ, hF]; ring
  rw [hid]
  have := abs_add_le (RHColDecomp0499.Rp n k - RpQ n k) (F * (γ n 81 rt k - γ n 81 (rval RHEntry22_0505.rq) k))
  have num : (104 : ℝ) * (4 * 255 / 10 ^ 32) + 34 / 10 ^ 25 ≤ 4 / 10 ^ 24 := by norm_num
  linarith

theorem Tp_repr {n k : ℕ} (hn : n ≤ 127) (hk : k ≤ 127) :
    ∃ E : ℝ, |E| ≤ 2 / 10 ^ 24 ∧
      RHColDecomp0499.Tp n k = (if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) -
        halfWidth * cc n * cc k * ((1 + (-1) ^ (n + k)) / 2) * TS n 82 gq k (n + k + 1) + E := by
  have hL := halfWidth_pos
  have he := Tp_err n k
  have hX := TpX_eq n k
  rw [S_split] at hX
  set σ : ℝ := (1 + (-1) ^ (n + k)) / 2 with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; rcases neg_one_pow_eq_or ℝ (n + k) with h | h <;> rw [h] <;> norm_num
  have hσ1 : σ ≤ 1 := by rw [hσ]; rcases neg_one_pow_eq_or ℝ (n + k) with h | h <;> rw [h] <;> norm_num
  set F := halfWidth * cc n * cc k with hF
  have hF0 : 0 ≤ F := by rw [hF]; exact mul_nonneg (mul_nonneg hL.le (cc_nonneg n)) (cc_nonneg k)
  have hFle : F ≤ 128 := Lcc_le hn hk
  set I := ∫ u in (-1:ℝ)..1, p n u * p k u
  have hLI : F * I = if n = k then 1 else 0 := Lcc n k
  set dG := ∑ i ∈ range 82, (gm i - gqv gq i) * ∑ l ∈ range (n + k + 1), V n k l * (2 / (2 * l + 1) * β 0 i l)
  have hdG : |dG| ≤ 2 / 10 ^ 32 := by
    have h1 : |dG| ≤ ∑ i ∈ range 82, (Dg i : ℝ) * (2 ^ i * 2) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => ?_))
      rw [abs_mul]; exact mul_le_mul (gm_close i) (X_bound n k i) (abs_nonneg _)
        (le_trans (abs_nonneg _) (gm_close i))
    have h2 : ∑ i ∈ range 82, (Dg i : ℝ) * (2 ^ i * 2) = 2 * ((Dgsum : ℚ) : ℝ) := by
      unfold Dgsum; push_cast; rw [mul_sum]; exact sum_congr rfl (fun i _ => by ring)
    have h3 : ((Dgsum : ℚ) : ℝ) ≤ 1 / 10 ^ 32 := by
      have := (Rat.cast_le (K := ℝ)).mpr Dgsum_le; push_cast at this; exact this
    linarith
  have hV0 : V n k 0 * muR 0 = I * (Real.log 2 - 1) := by rw [V0_eq]; simp only [muR]; ring
  have hX2 : TpX n k = (if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) -
      F * σ * (TS n 82 gq k (n + k + 1) + dG) := by
    rw [hX, hV0]
    have hI : F * I * (g0 - Real.log halfWidth) - F * I * σ * 2 * (Real.log 2 - 1) / 2 =
        (if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) := by
      rw [hLI]; split_ifs with h
      · subst h; rw [hσ, show n + n = 2 * n by ring, pow_mul]; norm_num
      · ring
    rw [← hI, hσ]; ring
  refine ⟨RHColDecomp0499.Tp n k - ((if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) -
      F * σ * TS n 82 gq k (n + k + 1)), ?_, by ring⟩
  rw [hX2] at he
  have hid : RHColDecomp0499.Tp n k - ((if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) -
      F * σ * TS n 82 gq k (n + k + 1)) = (RHColDecomp0499.Tp n k - ((if n = k then g0 - Real.log halfWidth -
      (Real.log 2 - 1) else 0) - F * σ * (TS n 82 gq k (n + k + 1) + dG))) - F * σ * dG := by ring
  rw [hid]
  have h1 := abs_sub (RHColDecomp0499.Tp n k - ((if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0) -
      F * σ * (TS n 82 gq k (n + k + 1) + dG))) (F * σ * dG)
  have h2 : |F * σ * dG| ≤ 128 * 1 * (2 / 10 ^ 32) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hF0, abs_of_nonneg hσ0]
    exact mul_le_mul (mul_le_mul hFle hσ1 hσ0 (by norm_num)) hdG (abs_nonneg _) (by norm_num)
  have h3 : 2 / 10 ^ 24 * halfWidth ≤ 2 / 10 ^ 24 * (81 / 100) := mul_le_mul_of_nonneg_left L_le (by positivity)
  have num : (128 : ℝ) * 1 * (2 / 10 ^ 32) + 2 / 10 ^ 24 * (81 / 100) ≤ 2 / 10 ^ 24 := by norm_num
  linarith

end RHEntryRepr0512

