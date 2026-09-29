import Iter0505
import Link0505

/-! # 0511: Legendre vectors of affinely transformed Legendre polynomials

`Af α γ l`: coefficients of `t ↦ P_l(α t + γ)`:
`Af 0 = δ_0`, `Af 1 = α XS δ_0 + γ δ_0`,
`Af (l+2) = ((2l+3)(α XS (Af (l+1)) + γ Af (l+1)) − (l+1) Af l)/(l+2)`.
`p l (α t + γ) = evV (l+1) (Af α γ l) t`, and
`∫_{−1}^1 P_n(αt+γ₁) P_k(αt+γ₂) dt = Σ_{j<N} A_j B_j · 2/(2j+1)`. -/

open Finset
open scoped BigOperators

namespace RHPrAff0511
open RHLeg0503 RHLegVec0503 RHSparse0504 RHIter0505

noncomputable def Af (α γ : ℝ) : ℕ → ℕ → ℝ
  | 0 => δ 0
  | 1 => fun j => α * XS (δ 0) j + γ * δ 0 j
  | l + 2 => fun j => ((2 * (l : ℝ) + 3) * (α * XS (Af α γ (l + 1)) j + γ * Af α γ (l + 1) j) -
      ((l : ℝ) + 1) * Af α γ l j) / ((l : ℝ) + 2)

lemma δ0_supp : ∀ j, 0 + 1 ≤ j → δ 0 j = 0 := fun j h => by simp [δ]; omega

theorem Af_supp (α γ : ℝ) : ∀ l j, l + 1 ≤ j → Af α γ l j = 0
  | 0, j, h => δ0_supp j (by omega)
  | 1, j, h => by
      simp only [Af]; rw [XS_zero δ0_supp j (by omega), δ0_supp j (by omega)]; ring
  | l + 2, j, h => by
      simp only [Af]
      rw [XS_zero (Af_supp α γ (l + 1)) j (by omega), Af_supp α γ (l + 1) j (by omega), Af_supp α γ l j (by omega)]
      ring

lemma evV_mono' {N N' : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (h : N ≤ N') (u : ℝ) :
    evV N' c u = evV N c u := by
  unfold evV; symm
  apply sum_subset (range_subset_range.mpr h)
  intro l _ hl; simp at hl; rw [hc l hl, zero_mul]

lemma evV_lin (N : ℕ) (a b : ℝ) (c d : ℕ → ℝ) (u : ℝ) :
    evV N (fun j => a * c j + b * d j) u = a * evV N c u + b * evV N d u := by
  unfold evV; rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl (fun j _ => by ring)

theorem aff_eq (α γ : ℝ) : ∀ (l : ℕ) (t : ℝ), p l (α * t + γ) = evV (l + 1) (Af α γ l) t
  | 0, t => by
      rw [p_zero]; unfold evV; simp [Af, δ, p_zero]
  | 1, t => by
      rw [p_one]
      have hx := X_evS δ0_supp t
      have h0 : evV (0 + 1) (δ 0) t = 1 := by unfold evV; simp [δ, p_zero]
      rw [h0, mul_one] at hx
      show α * t + γ = evV (1 + 1) (fun j => α * XS (δ 0) j + γ * δ 0 j) t
      rw [evV_lin, ← hx, evV_mono' δ0_supp (by omega), h0]; ring
  | l + 2, t => by
      have h1 := aff_eq α γ (l + 1) t
      have h0 := aff_eq α γ l t
      have hr := p_rec l (α * t + γ)
      have hx := X_evS (Af_supp α γ (l + 1)) t
      have hl : ((l : ℝ) + 2) ≠ 0 := by positivity
      have e : p (l + 2) (α * t + γ) = ((2 * (l : ℝ) + 3) * (α * (t * p (l + 1) (α * t + γ)) + γ * p (l + 1) (α * t + γ)) -
          ((l : ℝ) + 1) * p l (α * t + γ)) / ((l : ℝ) + 2) := by
        field_simp; linear_combination hr
      rw [e, h1, h0, hx]
      have hN : l + 1 + 1 + 1 = l + 2 + 1 := by omega
      rw [hN, ← evV_mono' (Af_supp α γ (l + 1)) (show l + 1 + 1 ≤ l + 2 + 1 by omega) t,
        ← evV_mono' (Af_supp α γ l) (show l + 1 ≤ l + 2 + 1 by omega) t]
      unfold evV
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, mul_sum, ← sum_sub_distrib, sum_div]
      refine sum_congr rfl (fun j _ => ?_)
      simp only [Af]
      ring

theorem aff_int (α γ₁ γ₂ : ℝ) (n k : ℕ) :
    ∫ t in (-1:ℝ)..1, p n (α * t + γ₁) * p k (α * t + γ₂) =
      ∑ j ∈ range (n + 1), Af α γ₁ n j * Af α γ₂ k j * (2 / (2 * j + 1)) := by
  have e : (fun t => p n (α * t + γ₁) * p k (α * t + γ₂)) =
      fun t => ∑ j ∈ range (n + 1), ∑ i ∈ range (k + 1), Af α γ₁ n j * Af α γ₂ k i * (p j t * p i t) := by
    funext t; rw [aff_eq, aff_eq]; unfold evV; rw [sum_mul_sum]
    exact sum_congr rfl (fun j _ => sum_congr rfl (fun i _ => by ring))
  rw [e, intervalIntegral.integral_finsetSum (f := fun j t => ∑ i ∈ range (k + 1), Af α γ₁ n j * Af α γ₂ k i * (p j t * p i t))
    (fun j _ => (continuous_finsetSum _ (fun i _ => continuous_const.mul ((continuous_p j).mul (continuous_p i)))).intervalIntegrable _ _)]
  refine sum_congr rfl (fun j hj => ?_)
  rw [intervalIntegral.integral_finsetSum (f := fun i t => Af α γ₁ n j * Af α γ₂ k i * (p j t * p i t))
    (fun i _ => (continuous_const.mul ((continuous_p j).mul (continuous_p i))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, RHLink0505.orth]
  by_cases h : j < k + 1
  · rw [sum_eq_single j (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero]) (fun h' => absurd (mem_range.mpr h) h'),
      if_pos rfl]
  · rw [Af_supp α γ₂ k j (by omega), sum_eq_zero (fun i hi => by simp at hi; rw [if_neg (by omega), mul_zero])]
    ring

end RHPrAff0511

