import PrAff0511
import RpExact0506

/-! # 0511: reduction of the prime-shift integrals

For `0 < s < 2L`, `σ = s/L`, `α = (2−σ)/2`:
* `Jm n k s = ∫_I zp b_n(x−s) b_k(x) = L α c_n c_k Σ_j Af α (−σ/2) n j · Af α (σ/2) k j · 2/(2j+1)`;
* `Jp n k s = ∫_I zp b_n(x+s) b_k(x) = (−1)^{n+k} Jm n k s`. -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace RHPrRed0511
open RHConditionalLog5 RHLog5Bridge RHLeg0503 RHLegVec0503 RHPrAff0511 RHRpExact0506 RHLowBlock0494

local notation "Lw" => halfWidth

noncomputable def Jm (n k : ℕ) (s : ℝ) : ℝ :=
  ∫ x in Icc (-Lw) Lw, zp (basisPoly n) (x - s) * (basisPoly k).eval x
noncomputable def Jp (n k : ℕ) (s : ℝ) : ℝ :=
  ∫ x in Icc (-Lw) Lw, zp (basisPoly n) (x + s) * (basisPoly k).eval x

@[fun_prop] lemma bp_cont (n : ℕ) : Continuous fun x => (basisPoly n).eval x := (basisPoly n).continuous

lemma setI_gen {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : ∫ x in Icc a b, f x = ∫ x in a..b, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- Support: `Jm = ∫_{−L+s}^{L} b_n(x−s) b_k(x)`. -/
lemma Jm_supp (n k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * Lw) :
    Jm n k s = ∫ x in (-Lw + s)..Lw, (basisPoly n).eval (x - s) * (basisPoly k).eval x := by
  have hL := halfWidth_pos
  unfold Jm
  have e : ∀ x ∈ Icc (-Lw) Lw, zp (basisPoly n) (x - s) * (basisPoly k).eval x =
      (Icc (-Lw + s) Lw).indicator (fun x => (basisPoly n).eval (x - s) * (basisPoly k).eval x) x := by
    intro x hx
    by_cases h : x ∈ Icc (-Lw + s) Lw
    · rw [indicator_of_mem h, zp_of_mem]; exact ⟨by linarith [h.1], by linarith [hx.2]⟩
    · rw [indicator_of_notMem h, zp_of_not_mem, zero_mul]
      intro h'; exact h ⟨by linarith [h'.1], hx.2⟩
  rw [setIntegral_congr_fun measurableSet_Icc e, setIntegral_indicator measurableSet_Icc, Icc_inter_Icc,
    max_eq_right (by linarith), min_self, setI_gen (by linarith)]

lemma Jp_supp (n k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * Lw) :
    Jp n k s = ∫ x in (-Lw)..(Lw - s), (basisPoly n).eval (x + s) * (basisPoly k).eval x := by
  have hL := halfWidth_pos
  unfold Jp
  have e : ∀ x ∈ Icc (-Lw) Lw, zp (basisPoly n) (x + s) * (basisPoly k).eval x =
      (Icc (-Lw) (Lw - s)).indicator (fun x => (basisPoly n).eval (x + s) * (basisPoly k).eval x) x := by
    intro x hx
    by_cases h : x ∈ Icc (-Lw) (Lw - s)
    · rw [indicator_of_mem h, zp_of_mem]; exact ⟨by linarith [hx.1], by linarith [h.2]⟩
    · rw [indicator_of_notMem h, zp_of_not_mem, zero_mul]
      intro h'; exact h ⟨hx.1, by linarith [h'.2]⟩
  rw [setIntegral_congr_fun measurableSet_Icc e, setIntegral_indicator measurableSet_Icc, Icc_inter_Icc,
    max_self, min_eq_right (by linarith), setI_gen (by linarith)]

lemma bparity (n : ℕ) (x : ℝ) : (basisPoly n).eval (-x) = (-1) ^ n * (basisPoly n).eval x := by
  rw [RHLink0505.basisPoly_eval, RHLink0505.basisPoly_eval, neg_div, p_neg]; ring

theorem Jp_eq (n k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * Lw) : Jp n k s = (-1) ^ (n + k) * Jm n k s := by
  rw [Jp_supp n k hs0 hs, Jm_supp n k hs0 hs, ← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_neg (a := -Lw + s) (b := Lw)
    (fun x => (basisPoly n).eval (x + s) * (basisPoly k).eval x)
  simp only [neg_add, neg_neg] at h
  rw [show Lw + -s = Lw - s by ring] at h
  rw [← h]
  congr 1; funext x
  rw [show -x + s = -(x - s) by ring, bparity, bparity, pow_add]; ring

theorem Jm_eq (n k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * Lw) :
    Jm n k s = Lw * ((2 - s / Lw) / 2) * cc n * cc k *
      ∑ j ∈ range (n + 1), Af ((2 - s / Lw) / 2) (-(s / Lw) / 2) n j * Af ((2 - s / Lw) / 2) (s / Lw / 2) k j *
        (2 / (2 * j + 1)) := by
  have hL := halfWidth_pos
  set σ := s / Lw with hσ
  set α := (2 - σ) / 2 with hα
  set κ := Lw * α with hκ
  have hκ0 : κ ≠ 0 := by
    have : σ < 2 := by rw [hσ, div_lt_iff₀ hL]; linarith
    rw [hκ, hα]; apply mul_ne_zero hL.ne'; linarith
  rw [Jm_supp n k hs0 hs.le, ← aff_int]
  have h := intervalIntegral.integral_comp_mul_add (a := -1) (b := 1)
    (fun x => (basisPoly n).eval (x - s) * (basisPoly k).eval x) hκ0 (s / 2)
  have e1 : κ * -1 + s / 2 = -Lw + s := by rw [hκ, hα, hσ]; field_simp; ring
  have e2 : κ * 1 + s / 2 = Lw := by rw [hκ, hα, hσ]; field_simp; ring
  rw [e1, e2, smul_eq_mul] at h
  have h' : (∫ x in (-Lw + s)..Lw, (basisPoly n).eval (x - s) * (basisPoly k).eval x) =
      κ * ∫ t in (-1:ℝ)..1, (basisPoly n).eval (κ * t + s / 2 - s) * (basisPoly k).eval (κ * t + s / 2) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hκ0, one_mul]
  rw [h', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [RHLink0505.basisPoly_eval, RHLink0505.basisPoly_eval]
  have a1 : (κ * t + s / 2 - s) / Lw = α * t + -σ / 2 := by rw [hκ, hσ]; field_simp; ring
  have a2 : (κ * t + s / 2) / Lw = α * t + σ / 2 := by rw [hκ, hσ]; field_simp
  rw [a1, a2]; unfold cc; ring

end RHPrRed0511

