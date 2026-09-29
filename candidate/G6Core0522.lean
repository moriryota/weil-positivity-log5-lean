import PrBall0511
import TabCore0515

/-! # 0522: generic ball soundness for the G6c stages

* `vecMem_take`: a `RowMem` row (valid prefix) truncated to `N` entries is `VecMem` of the truncated
  real function `j ↦ if j < N then f j else 0`.
* `dotRows_mem`: `(Ml.map (dotB S · Bl))` encloses `j ↦ Σ_{j'<N} M j j' · B j'` entrywise.
* `bil_mem`: `dotB S Al (dotRows Ml Bl)` encloses `Σ_{j<N} Σ_{j'<N} A j · M j j' · B j'`.
 -/

open Finset
open scoped BigOperators

namespace RHG6Core0522
open RHBall0504 RHBallVec0504 RHBallDot0509 RHRec2D0515

/-- Truncate `f` to its first `N` values. -/
noncomputable def trunc (N : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := fun j => if j < N then f j else 0

lemma vecMem_take {S : ℕ} (hS : 0 < S) {f : ℕ → ℝ} {bs : List Ball} (h : RowMem S f bs) {N : ℕ}
    (hN : N ≤ bs.length) : VecMem S (trunc N f) (bs.take N) := by
  intro j
  unfold trunc gz
  by_cases hj : j < N
  · rw [if_pos hj, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj,
      ← List.getD_eq_getElem?_getD]
    exact h j (by omega)
  · rw [if_neg hj, List.getD_eq_getElem?_getD, List.getElem?_take, if_neg hj]
    simp [mem_zero _ hS]

lemma sum_range_of_supp {N M : ℕ} (hNM : N ≤ M) {g : ℕ → ℝ} (hg : ∀ j, N ≤ j → g j = 0) :
    ∑ j ∈ range M, g j = ∑ j ∈ range N, g j := by
  symm; apply sum_subset (range_subset_range.mpr hNM)
  intro j _ hj; simp at hj; exact hg j hj

/-- A vector list of length `N` enclosing `c`; sums over `range N` then equal `dotB` sums. -/
theorem dot_mem {S : ℕ} (hS : 0 < S) {c d : ℕ → ℝ} {as bs : List Ball} (hc : VecMem S c as) (hd : VecMem S d bs)
    (N : ℕ) (hc0 : ∀ j, N ≤ j → c j = 0) (hd0 : ∀ j, N ≤ j → d j = 0) :
    mem S (∑ j ∈ range N, c j * d j) (dotB S as bs) := by
  have h := mem_dotB hS as bs c d hc hd
  have ha : ∀ j, as.length ≤ j → c j = 0 := fun j hj => zero_of_len hS hc hj
  have hb : ∀ j, bs.length ≤ j → d j = 0 := fun j hj => zero_of_len hS hd hj
  have e1 : ∑ l ∈ range (max N (max as.length bs.length)), c l * d l =
      ∑ l ∈ range (min as.length bs.length), c l * d l := by
    refine sum_range_of_supp (by omega) (fun j hj => ?_)
    rcases Nat.le_total as.length bs.length with hl | hl
    · rw [min_eq_left hl] at hj; rw [ha j hj, zero_mul]
    · rw [min_eq_right hl] at hj; rw [hb j hj, mul_zero]
  have e2 : ∑ l ∈ range (max N (max as.length bs.length)), c l * d l = ∑ l ∈ range N, c l * d l :=
    sum_range_of_supp (by omega) (fun j hj => by rw [hc0 j hj, zero_mul])
  rw [← e2, e1]; exact h

def dotRows (S : ℕ) (Ml : List (List Ball)) (Bl : List Ball) : List Ball := Ml.map (fun row => dotB S row Bl)

theorem dotRows_mem {S : ℕ} (hS : 0 < S) {M : ℕ → ℕ → ℝ} {B : ℕ → ℝ} {Ml : List (List Ball)} {Bl : List Ball}
    (N : ℕ) (hlen : Ml.length = N) (hM : ∀ j < N, VecMem S (M j) (Ml.getD j [])) (hB : VecMem S B Bl)
    (hM0 : ∀ j < N, ∀ j', N ≤ j' → M j j' = 0) (hB0 : ∀ j, N ≤ j → B j = 0) :
    VecMem S (fun j => if j < N then ∑ j' ∈ range N, M j j' * B j' else 0) (dotRows S Ml Bl) := by
  intro j
  unfold dotRows gz
  beta_reduce
  by_cases hj : j < N
  · rw [if_pos hj, List.getD_eq_getElem?_getD, List.getElem?_map]
    have hj' : j < Ml.length := by omega
    rw [List.getElem?_eq_getElem hj']
    simp only [Option.map_some, Option.getD_some]
    have := dot_mem hS (hM j hj) hB N (hM0 j hj) hB0
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using this
  · rw [if_neg hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega)]
    simp [mem_zero _ hS]

theorem bil_mem {S : ℕ} (hS : 0 < S) {A B : ℕ → ℝ} {M : ℕ → ℕ → ℝ} {Al Bl : List Ball} {Ml : List (List Ball)}
    (N : ℕ) (hlen : Ml.length = N) (hA : VecMem S A Al) (hB : VecMem S B Bl)
    (hM : ∀ j < N, VecMem S (M j) (Ml.getD j []))
    (hM0 : ∀ j < N, ∀ j', N ≤ j' → M j j' = 0) (hA0 : ∀ j, N ≤ j → A j = 0) (hB0 : ∀ j, N ≤ j → B j = 0) :
    mem S (∑ j ∈ range N, ∑ j' ∈ range N, A j * B j' * M j j') (dotB S Al (dotRows S Ml Bl)) := by
  have hY := dotRows_mem hS N hlen hM hB hM0 hB0
  have h := dot_mem hS hA hY N hA0 (fun j hj => by simp [show ¬ j < N by omega])
  convert h using 1
  refine sum_congr rfl (fun j hj => ?_)
  rw [if_pos (mem_range.mp hj), mul_sum]
  exact sum_congr rfl (fun j' _ => by ring)

end RHG6Core0522

