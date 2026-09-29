import Entry00Bounds0495
import PiBounds0466

/-! # 0510: rational enclosures of `log L` (L = log 5 / 2) and of the Tp diagonal constant

`log L ∈ [LLlo, LLhi]` (width 2e-29) from `log 5 ∈ [l5L, l5H]` and Mathlib's
`Real.abs_log_sub_add_sum_range_le` (40 terms, `decide +kernel` on rationals).
`Cd = 2 log 2 + π/2 − log L − (log 2 − 1)`. -/

open Finset
open scoped BigOperators

namespace RHConst0510
open RHLog5Bridge RHEntry00Bounds0495

def lsum (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, x ^ (i + 1) / (i + 1)

lemma log_near (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |((lsum x n : ℚ) : ℝ) + Real.log (1 - x)| ≤ (((x ^ (n + 1) / (1 - x)) : ℚ) : ℝ) := by
  have hx0 : (0:ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x:ℝ) < 1 := by exact_mod_cast h1
  have h := Real.abs_log_sub_add_sum_range_le (x := (x:ℝ)) (by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at h
  unfold lsum; push_cast; exact h

def xL : ℚ := 1 - l5L / 2
def xH : ℚ := 1 - l5H / 2
def LLlo : ℚ := -1086310926164173441973574539558151365901 / 5000000000000000000000000000000000000000
def LLhi : ℚ := -2172621852328346883947149078910912038561 / 10000000000000000000000000000000000000000

lemma chk_lo : LLlo ≤ -lsum xL 40 - xL ^ 41 / (1 - xL) := by decide +kernel
lemma chk_hi : -lsum xH 40 + xH ^ 41 / (1 - xH) ≤ LLhi := by decide +kernel
lemma xL_ok : 0 ≤ xL ∧ xL < 1 := by constructor <;> decide +kernel
lemma xH_ok : 0 ≤ xH ∧ xH < 1 := by constructor <;> decide +kernel

theorem logL_bounds : (LLlo : ℝ) ≤ Real.log halfWidth ∧ Real.log halfWidth ≤ (LLhi : ℝ) := by
  have h5 := b_l5
  have hLlo : ((1 - xL : ℚ) : ℝ) ≤ halfWidth := by unfold xL halfWidth; push_cast; linarith [h5.1]
  have hLhi : halfWidth ≤ ((1 - xH : ℚ) : ℝ) := by unfold xH halfWidth; push_cast; linarith [h5.2]
  have hpos : (0:ℝ) < ((1 - xL : ℚ) : ℝ) := by
    have : (0:ℚ) < 1 - xL := by linarith [xL_ok.2]
    exact_mod_cast this
  constructor
  · have hn := log_near xL xL_ok.1 xL_ok.2 40
    have hm : Real.log ((1 - xL : ℚ) : ℝ) ≤ Real.log halfWidth := Real.log_le_log hpos hLlo
    have hc := (Rat.cast_le (K := ℝ)).mpr chk_lo
    push_cast at hn hm hc ⊢
    have := (abs_le.mp hn).1
    linarith
  · have hn := log_near xH xH_ok.1 xH_ok.2 40
    have hm : Real.log halfWidth ≤ Real.log ((1 - xH : ℚ) : ℝ) := Real.log_le_log halfWidth_pos hLhi
    have hc := (Rat.cast_le (K := ℝ)).mpr chk_hi
    push_cast at hn hm hc ⊢
    have := (abs_le.mp hn).2
    linarith

end RHConst0510

