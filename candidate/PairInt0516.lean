import SingDef0516
import Rec2D0515
import Nu0514

/-! # 0516: pair integrals of the pieces of `φ_n` over `[−1,1]`

For `0 ≤ s, t ≤ 2`:
* `∫ pm_i(s) pm_k(t) = OO i k s t = ∫_{max s t − 1}^1 P_i(u−s) P_k(u−t)`;
* `∫ pp_i(s) pp_k(t) = (−1)^{i+k} OO i k s t`;
* `∫ pm_i(s) pp_k(t) = X i k s t = ∫_{s−1}^{1−t} P_i(u−s) P_k(u+t)` if `s + t ≤ 2`, `0` if `2 ≤ s + t`;
* `∫ lg P_i pm_k(s) = F i k s = ∫_{s−1}^1 lg P_i(u) P_k(u−s)`, `∫ lg P_i pp_k(s) = (−1)^{i+k} F i k s`.
 -/

open Set MeasureTheory intervalIntegral

namespace RHPairInt0516
open RHLeg0503 RHSingDef0516 RHRec2D0515

noncomputable def OO (i k : ℕ) (s t : ℝ) : ℝ := ∫ u in (max s t - 1)..1, p i (u - s) * p k (u - t)
noncomputable def X (i k : ℕ) (s t : ℝ) : ℝ := ∫ u in (s - 1)..(1 - t), p i (u - s) * p k (u + t)
noncomputable def F (i k : ℕ) (s : ℝ) : ℝ := ∫ u in (s - 1)..1, lg u * p i u * p k (u - s)

lemma lg_neg (u : ℝ) : lg (-u) = lg u := by unfold lg; ring_nf

lemma refl {a b : ℝ} (f : ℝ → ℝ) : ∫ u in a..b, f (-u) = ∫ u in (-b)..(-a), f u :=
  intervalIntegral.integral_comp_neg f

/-- `∫_a^b [u ≤ c] f = ∫_a^c f` for `a ≤ c ≤ b`. -/
lemma int_le_gen {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    ∫ u in a..b, (if u ≤ c then f u else 0) = ∫ u in a..c, f u := by
  have e : (fun u => if u ≤ c then f u else 0) = (Iic c).indicator f := by
    funext u; simp [Set.indicator_apply]
  rw [e, intervalIntegral.integral_of_le (hac.trans hcb), intervalIntegral.integral_of_le hac,
    setIntegral_indicator measurableSet_Iic]
  have hs : Ioc a b ∩ Iic c = Ioc a c := by
    ext u; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [hs]

theorem P1 (i k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    ∫ u in (-1:ℝ)..1, pm i s u * pm k t u = OO i k s t := by
  have e : ∀ u, pm i s u * pm k t u = if max s t - 1 < u then p i (u - s) * p k (u - t) else 0 := by
    intro u
    have hc : max s t - 1 < u ↔ s - 1 < u ∧ t - 1 < u := by rw [← max_sub_sub_right, max_lt_iff]
    by_cases h1 : s - 1 < u <;> by_cases h2 : t - 1 < u <;> simp [pm, h1, h2, hc]
  simp only [e]
  rw [int_gt (by have := le_max_left s t; linarith) (by have := max_le hs2 ht2; linarith)]
  rfl

theorem P2 (i k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    ∫ u in (-1:ℝ)..1, pp i s u * pp k t u = (-1) ^ (i + k) * OO i k s t := by
  have e : ∀ u, pp i s u * pp k t u = if u ≤ 1 - max s t then p i (u + s) * p k (u + t) else 0 := by
    intro u
    have hc : u ≤ 1 - max s t ↔ u ≤ 1 - s ∧ u ≤ 1 - t := by
      constructor
      · intro h; exact ⟨by linarith [le_max_left s t], by linarith [le_max_right s t]⟩
      · rintro ⟨h1, h2⟩
        rcases le_total s t with h | h
        · rw [max_eq_right h]; exact h2
        · rw [max_eq_left h]; exact h1
    by_cases h1 : u ≤ 1 - s <;> by_cases h2 : u ≤ 1 - t <;> simp [pp, h1, h2, hc]
  simp only [e]
  rw [int_le (by have := max_le hs2 ht2; linarith) (by have := le_max_left s t; linarith)]
  unfold OO
  rw [← intervalIntegral.integral_const_mul]
  have h := refl (a := max s t - 1) (b := 1) (fun u => p i (u + s) * p k (u + t))
  rw [show -(max s t - 1) = 1 - max s t by ring] at h
  rw [← h]
  congr 1; funext u
  rw [show -u + s = -(u - s) by ring, show -u + t = -(u - t) by ring, p_neg, p_neg, pow_add]; ring

theorem P3 (i k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 2) :
    ∫ u in (-1:ℝ)..1, pm i s u * pp k t u = X i k s t := by
  have e : ∀ u, pm i s u * pp k t u =
      if s - 1 < u then (if u ≤ 1 - t then p i (u - s) * p k (u + t) else 0) else 0 := by
    intro u
    by_cases h1 : s - 1 < u <;> by_cases h2 : u ≤ 1 - t <;> simp [pm, pp, h1, h2]
  simp only [e]
  rw [int_gt (by linarith) (by linarith), int_le_gen (by linarith) (by linarith)]
  rfl

theorem P3z (i k : ℕ) {s t : ℝ} (hst : 2 ≤ s + t) :
    ∫ u in (-1:ℝ)..1, pm i s u * pp k t u = 0 := by
  have e : ∀ u, pm i s u * pp k t u = 0 := by
    intro u
    by_cases h1 : s - 1 < u
    · have h2 : ¬ u ≤ 1 - t := by intro h; linarith
      simp [pp, h2]
    · simp [pm, h1]
  simp only [e, intervalIntegral.integral_zero]

theorem P4 (i k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 2) :
    ∫ u in (-1:ℝ)..1, pp i s u * pm k t u = X k i t s := by
  rw [← P3 k i ht hs (by linarith)]
  congr 1; funext u; ring

theorem P4z (i k : ℕ) {s t : ℝ} (hst : 2 ≤ s + t) :
    ∫ u in (-1:ℝ)..1, pp i s u * pm k t u = 0 := by
  rw [← P3z k i (s := t) (t := s) (by linarith)]
  congr 1; funext u; ring

theorem P5 (i k : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    ∫ u in (-1:ℝ)..1, lg u * p i u * pm k s u = F i k s := by
  have e : ∀ u, lg u * p i u * pm k s u = if s - 1 < u then lg u * p i u * p k (u - s) else 0 := by
    intro u; by_cases h1 : s - 1 < u <;> simp [pm, h1]
  simp only [e]
  rw [int_gt (by linarith) (by linarith)]
  rfl

theorem P6 (i k : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    ∫ u in (-1:ℝ)..1, lg u * p i u * pp k s u = (-1) ^ (i + k) * F i k s := by
  have e : ∀ u, lg u * p i u * pp k s u = if u ≤ 1 - s then lg u * p i u * p k (u + s) else 0 := by
    intro u; by_cases h1 : u ≤ 1 - s <;> simp [pp, h1]
  simp only [e]
  rw [int_le (by linarith) (by linarith)]
  unfold F
  rw [← intervalIntegral.integral_const_mul]
  have h := refl (a := s - 1) (b := 1) (fun u => lg u * p i u * p k (u + s))
  rw [show -(s - 1) = 1 - s by ring] at h
  rw [← h]
  congr 1; funext u
  rw [lg_neg, show -u + s = -(u - s) by ring, p_neg, p_neg, pow_add]; ring

end RHPairInt0516

