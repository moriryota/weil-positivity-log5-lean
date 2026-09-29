import Iter0505

/-! # 0508: Legendre expansion of products `P_n · P_k`

`V n 0 = δ_n`, `V n 1 = XS δ_n`, `V n (k+2) = ((2k+3)·XS (V n (k+1)) − (k+1)·V n k)/(k+2)`.
`p n u · p k u = evV (n+k+1) (V n k) u`. -/

open Finset
open scoped BigOperators

namespace RHProd0508
open RHLeg0503 RHLegVec0503 RHSparse0504 RHIter0505

noncomputable def V (n : ℕ) : ℕ → ℕ → ℝ
  | 0 => δ n
  | 1 => XS (δ n)
  | k + 2 => fun l => ((2 * (k : ℝ) + 3) * XS (V n (k + 1)) l - ((k : ℝ) + 1) * V n k l) / ((k : ℝ) + 2)

lemma evV_mono {N N' : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (h : N ≤ N') (u : ℝ) :
    RHLegVec0503.evV N' c u = RHLegVec0503.evV N c u := by
  unfold RHLegVec0503.evV
  symm
  apply sum_subset (range_subset_range.mpr h)
  intro l _ hl; simp at hl; rw [hc l hl, zero_mul]

lemma δ_supp (n : ℕ) : ∀ l, n + 1 ≤ l → δ n l = 0 := fun l h => by simp [δ]; omega

theorem V_supp (n : ℕ) : ∀ k l, n + k + 1 ≤ l → V n k l = 0
  | 0, l, h => δ_supp n l (by omega)
  | 1, l, h => XS_zero (δ_supp n) l (by omega)
  | k + 2, l, h => by
      simp only [V]
      rw [XS_zero (V_supp n (k + 1)) l (by omega), V_supp n k l (by omega)]
      simp

theorem prod_eq (n : ℕ) : ∀ k (u : ℝ), p n u * p k u = RHLegVec0503.evV (n + k + 1) (V n k) u
  | 0, u => by
      rw [p_zero, mul_one]
      have := congrFun (p_eq_evV n) u
      simpa [V] using this
  | 1, u => by
      rw [p_one, mul_comm]
      have h := X_evS (δ_supp n) u
      rw [← congrFun (p_eq_evV n) u] at h
      exact h
  | k + 2, u => by
      have h1 := prod_eq n (k + 1) u
      have h0 := prod_eq n k u
      have hr := p_rec k u
      have hx := X_evS (V_supp n (k + 1)) u
      have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
      -- p n u * p (k+2) u = ((2k+3) u (p n p(k+1)) − (k+1) p n p k)/(k+2)
      have e : p n u * p (k + 2) u =
          ((2 * (k : ℝ) + 3) * (u * (p n u * p (k + 1) u)) - ((k : ℝ) + 1) * (p n u * p k u)) / ((k : ℝ) + 2) := by
        field_simp
        linear_combination (p n u) * hr
      rw [e, h1, h0, hx]
      have hN : n + (k + 1) + 1 + 1 = n + (k + 2) + 1 := by ring
      rw [hN, ← evV_mono (V_supp n k) (show n + k + 1 ≤ n + (k + 2) + 1 by omega) u]
      unfold RHLegVec0503.evV
      rw [mul_sum, mul_sum, ← sum_sub_distrib, sum_div]
      refine sum_congr rfl (fun l _ => ?_)
      simp only [V]
      ring

end RHProd0508

