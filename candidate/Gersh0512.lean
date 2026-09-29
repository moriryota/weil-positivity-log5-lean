import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # 0512: Gershgorin-type lower bound for a quadratic form

If `M i i − ½ Σ_{j≠i} (|M i j| + |M j i|) ≥ μ` for all `i`, then `Σ_{i,j} c_i c_j M i j ≥ μ Σ_i c_i²`.
No symmetry assumption. -/

open Finset
open scoped BigOperators

namespace RHGersh0512

theorem gersh {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → ι → ℝ) (μ : ℝ)
    (h : ∀ i, μ ≤ M i i - (1/2) * ∑ j ∈ univ.erase i, (|M i j| + |M j i|)) (c : ι → ℝ) :
    μ * ∑ i, c i ^ 2 ≤ ∑ i, ∑ j, c i * c j * M i j := by
  -- split diagonal / off-diagonal
  have hsplit : ∑ i, ∑ j, c i * c j * M i j =
      ∑ i, c i ^ 2 * M i i + ∑ i, ∑ j ∈ univ.erase i, c i * c j * M i j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← add_sum_erase _ _ (mem_univ i)]; ring
  -- off-diagonal lower bound
  have hoff : ∀ i j, -(|M i j| * (c i ^ 2 + c j ^ 2) / 2) ≤ c i * c j * M i j := by
    intro i j
    have h1 : |c i * c j| ≤ (c i ^ 2 + c j ^ 2) / 2 := by
      rw [abs_mul]; nlinarith [sq_nonneg (|c i| - |c j|), sq_abs (c i), sq_abs (c j)]
    have h2 : |c i * c j * M i j| ≤ (c i ^ 2 + c j ^ 2) / 2 * |M i j| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have := neg_abs_le (c i * c j * M i j)
    linarith
  have hsum : ∑ i, ∑ j ∈ univ.erase i, -(|M i j| * (c i ^ 2 + c j ^ 2) / 2) ≤
      ∑ i, ∑ j ∈ univ.erase i, c i * c j * M i j :=
    sum_le_sum (fun i _ => sum_le_sum (fun j _ => hoff i j))
  -- rearrange the off-diagonal bound
  have hre : ∑ i, ∑ j ∈ univ.erase i, (|M i j| * (c i ^ 2 + c j ^ 2) / 2) =
      ∑ i, c i ^ 2 * ((1/2) * ∑ j ∈ univ.erase i, (|M i j| + |M j i|)) := by
    have e1 : ∑ i, ∑ j ∈ univ.erase i, (|M i j| * (c i ^ 2 + c j ^ 2) / 2) =
        ∑ i, ∑ j ∈ univ.erase i, |M i j| * c i ^ 2 / 2 + ∑ i, ∑ j ∈ univ.erase i, |M i j| * c j ^ 2 / 2 := by
      rw [← sum_add_distrib]; exact sum_congr rfl (fun i _ => by rw [← sum_add_distrib]; exact sum_congr rfl (fun j _ => by ring))
    have e2 : ∑ i, ∑ j ∈ univ.erase i, |M i j| * c j ^ 2 / 2 = ∑ i, ∑ j ∈ univ.erase i, |M j i| * c i ^ 2 / 2 := by
      have : ∀ f : ι → ι → ℝ, ∑ i, ∑ j ∈ univ.erase i, f i j = ∑ i, ∑ j, if j = i then 0 else f i j := by
        intro f; refine sum_congr rfl (fun i _ => ?_)
        rw [sum_ite, filter_eq', if_pos (mem_univ i), sum_singleton, zero_add]
        congr 1; ext j; simp [and_comm, ne_comm]
      rw [this (fun i j => |M i j| * c j ^ 2 / 2), this (fun i j => |M j i| * c i ^ 2 / 2), sum_comm]
      refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [e1, e2, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← sum_add_distrib, mul_sum, mul_sum]
    exact sum_congr rfl (fun j _ => by ring)
  have hlow : ∑ i, c i ^ 2 * (μ + (1/2) * ∑ j ∈ univ.erase i, (|M i j| + |M j i|)) ≤ ∑ i, c i ^ 2 * M i i :=
    sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (by linarith [h i]) (sq_nonneg _))
  have e3 : ∑ i, c i ^ 2 * (μ + (1/2) * ∑ j ∈ univ.erase i, (|M i j| + |M j i|)) =
      μ * ∑ i, c i ^ 2 + ∑ i, c i ^ 2 * ((1/2) * ∑ j ∈ univ.erase i, (|M i j| + |M j i|)) := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl (fun i _ => by ring)
  have e4 : ∑ i, ∑ j ∈ univ.erase i, -(|M i j| * (c i ^ 2 + c j ^ 2) / 2) =
      -∑ i, ∑ j ∈ univ.erase i, (|M i j| * (c i ^ 2 + c j ^ 2) / 2) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl (fun i _ => by rw [← sum_neg_distrib])
  rw [hsplit]
  rw [e4, hre] at hsum
  rw [e3] at hlow
  linarith

end RHGersh0512

