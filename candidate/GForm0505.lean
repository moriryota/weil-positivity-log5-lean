import Iter0505
import Link0505

/-! # 0505: the inner integral as a Legendre vector, and the entry formula

For `R(w) = Σ_{j<J} r_j w^j` and `u ∈ [−1,1]`:
`∫_{−1}^1 R(|u−v|) (P_n(u) − P_n(v)) dv = evV (n+1+J) (γ n J r) u` with
`γ l = Σ_j r_j [ (β_{j+1,l} + (−1)^{n+l} β_{j+1,l})/(j+1) − j!·(α_{j+1,l} + (−1)^{n+l} α_{j+1,l}) ]`,
hence `∫_{−1}^1 P_k(u) ∫ R(|u−v|)(P_n(u) − P_n(v)) dv du = 2/(2k+1) · γ k`. -/

open Finset intervalIntegral
open scoped BigOperators

namespace RHGForm0505
open RHLeg0503 RHCauchy0503 RHLegVec0503 RHSparse0504 RHIter0505

@[fun_prop] lemma cont_p (n : ℕ) : Continuous fun x => p n x := continuous_p n

lemma evV_mono {N N' : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (h : N ≤ N') (u : ℝ) :
    evV N' c u = evV N c u := by
  unfold evV
  symm
  apply sum_subset (range_subset_range.mpr h)
  intro l _ hl; simp at hl; rw [hc l hl, zero_mul]

lemma evV_add (N : ℕ) (c d : ℕ → ℝ) (u : ℝ) : evV N (fun l => c l + d l) u = evV N c u + evV N d u := by
  unfold evV; rw [← sum_add_distrib]; exact sum_congr rfl (fun l _ => by ring)

lemma evV_smul (N : ℕ) (a : ℝ) (c : ℕ → ℝ) (u : ℝ) : evV N (fun l => a * c l) u = a * evV N c u := by
  unfold evV; rw [mul_sum]; exact sum_congr rfl (fun l _ => by ring)

lemma evV_sum (N J : ℕ) (f : ℕ → ℕ → ℝ) (u : ℝ) :
    evV N (fun l => ∑ j ∈ range J, f j l) u = ∑ j ∈ range J, evV N (f j) u := by
  unfold evV; rw [sum_comm]; exact sum_congr rfl (fun l _ => by rw [sum_mul])

noncomputable def refl (c : ℕ → ℝ) (l : ℕ) : ℝ := (-1) ^ l * c l

noncomputable def γ (n J : ℕ) (r : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ j ∈ range J, r j * ((β n (j + 1) l + (-1) ^ n * refl (β n (j + 1)) l) / (j + 1) -
    (j.factorial : ℝ) * (α n (j + 1) l + (-1) ^ n * refl (α n (j + 1)) l))

/-- `(1−u)^m P_n(u) = (−1)^n · evV (β n m) (−u)`. -/
lemma oneMinus_p (n m : ℕ) (u : ℝ) :
    (1 - u) ^ m * p n u = (-1) ^ n * evV (n + 1 + m) (β n m) (-u) := by
  rw [← onePlus_p n m (-u), p_neg n u]
  have h1 : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-((1 - u) ^ m * p n u)) * h1

/-- One power: `∫ |u−v|^j (P_n(u) − P_n(v)) dv` as a Legendre vector (length `n+2+j`). -/
lemma one_power (n j : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    ∫ v in (-1:ℝ)..1, |u - v| ^ j * (p n u - p n v) =
      evV (n + 1 + (j + 1)) (fun l => (β n (j + 1) l + (-1) ^ n * refl (β n (j + 1)) l) / (j + 1) -
        (j.factorial : ℝ) * (α n (j + 1) l + (-1) ^ n * refl (α n (j + 1)) l)) u := by
  have hc1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  have hW := abs_pow_split j hc1 hu
  have hK := abs_pow_split j (continuous_p n) hu
  have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by push_cast [Nat.factorial_succ]; ring
  rw [Im_iter_one, Ip_iter_one, hf] at hW
  rw [Im_iter_p, Ip_iter_p, Im_iter_p] at hK
  have split : (∫ v in (-1:ℝ)..1, |u - v| ^ j * (p n u - p n v)) =
      p n u * (∫ v in (-1:ℝ)..1, |u - v| ^ j * 1) - ∫ v in (-1:ℝ)..1, |u - v| ^ j * p n v := by
    rw [← integral_const_mul, ← integral_sub]
    · congr 1; funext v; ring
    · exact (by fun_prop : Continuous fun v => p n u * (|u - v| ^ j * 1)).intervalIntegrable _ _
    · exact ((by fun_prop : Continuous fun v => |u - v| ^ j).mul (continuous_p n)).intervalIntegrable _ _
  rw [split, hW, hK]
  have hβ1 := onePlus_p n (j + 1) u
  have hβ2 := oneMinus_p n (j + 1) u
  rw [evV_neg] at hβ2
  rw [evV_neg]
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  -- expand the right-hand side
  have eR : evV (n + 1 + (j + 1)) (fun l => (β n (j + 1) l + (-1) ^ n * refl (β n (j + 1)) l) / (j + 1) -
        (j.factorial : ℝ) * (α n (j + 1) l + (-1) ^ n * refl (α n (j + 1)) l)) u =
      (evV (n + 1 + (j + 1)) (β n (j + 1)) u +
        (-1) ^ n * evV (n + 1 + (j + 1)) (fun l => (-1) ^ l * β n (j + 1) l) u) / (j + 1) -
      (j.factorial : ℝ) * (evV (n + 1 + (j + 1)) (α n (j + 1)) u +
        (-1) ^ n * evV (n + 1 + (j + 1)) (fun l => (-1) ^ l * α n (j + 1) l) u) := by
    unfold evV refl
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, sum_div, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun l _ => by ring)
  rw [eR, ← hβ1, ← hβ2]
  field_simp

theorem G_eq (n J : ℕ) (r : ℕ → ℝ) {u : ℝ} (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, r j * |u - v| ^ j) * (p n u - p n v) =
      evV (n + 1 + J) (γ n J r) u := by
  have hint : ∀ j ∈ range J, IntervalIntegrable (fun v => r j * (|u - v| ^ j * (p n u - p n v)))
      MeasureTheory.volume (-1) 1 := fun j _ =>
    (by fun_prop : Continuous fun v => r j * (|u - v| ^ j * (p n u - p n v))).intervalIntegrable _ _
  have e1 : (fun v => (∑ j ∈ range J, r j * |u - v| ^ j) * (p n u - p n v)) =
      fun v => ∑ j ∈ range J, r j * (|u - v| ^ j * (p n u - p n v)) := by
    funext v; rw [sum_mul]; exact sum_congr rfl (fun j _ => by ring)
  rw [e1, integral_finsetSum hint]
  unfold γ
  rw [evV_sum]
  refine sum_congr rfl (fun j hj => ?_)
  rw [integral_const_mul, one_power n j hu, evV_smul]
  congr 1
  simp at hj
  have hz : ∀ l, n + 1 + (j + 1) ≤ l → ((β n (j + 1) l + (-1) ^ n * refl (β n (j + 1)) l) / (j + 1) -
      (j.factorial : ℝ) * (α n (j + 1) l + (-1) ^ n * refl (α n (j + 1)) l)) = 0 := by
    intro l hl
    simp only [refl]
    rw [α_supp n (j + 1) l hl, β_supp n (j + 1) l hl]
    simp
  exact (evV_mono hz (by omega) u).symm

/-- Entry formula: `∫ P_k(u) · (∫ R(|u−v|)(P_n(u) − P_n(v)) dv) du = 2/(2k+1) · γ k`. -/
theorem entry_eq (n J k : ℕ) (r : ℕ → ℝ) :
    ∫ u in (-1:ℝ)..1, p k u * ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, r j * |u - v| ^ j) * (p n u - p n v) =
      2 / (2 * k + 1) * γ n J r k := by
  have e : ∀ u ∈ Set.uIcc (-1:ℝ) 1,
      p k u * (∫ v in (-1:ℝ)..1, (∑ j ∈ range J, r j * |u - v| ^ j) * (p n u - p n v)) =
      ∑ l ∈ range (n + 1 + J), γ n J r l * (p k u * p l u) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    rw [G_eq n J r hu, evV, mul_sum]
    exact sum_congr rfl (fun l _ => by ring)
  rw [integral_congr e, integral_finsetSum
    (fun l _ => ((by fun_prop : Continuous fun u => p k u * p l u).const_mul _ |>.intervalIntegrable _ _))]
  simp_rw [integral_const_mul, RHLink0505.orth]
  by_cases hk : k < n + 1 + J
  · rw [sum_eq_single k (fun l _ hl => by rw [if_neg (Ne.symm hl), mul_zero]) (fun h => absurd (mem_range.mpr hk) h)]
    rw [if_pos rfl]; ring
  · have hz : γ n J r k = 0 := by
      unfold γ
      refine sum_eq_zero (fun j hj => ?_)
      simp at hj
      simp only [refl]
      rw [α_supp n (j + 1) k (by omega), β_supp n (j + 1) k (by omega)]
      simp
    rw [hz, mul_zero]
    refine sum_eq_zero (fun l hl => ?_)
    simp at hl
    rw [if_neg (by omega), mul_zero]

end RHGForm0505

