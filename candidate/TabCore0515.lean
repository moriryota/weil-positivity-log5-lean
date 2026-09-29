import Rec2D0515
import BallMisc0512

/-! # 0515: literal moment tables checked by the kernel

* `ratBall S N D = (⌊N·S/D⌋, 1)` encloses `N/D` (`D > 0`).
* `chkFrom j tab`: every consecutive triple of rows satisfies the `tnext` recurrence (starting at row
  index `j`); `chk1 tab`: row 1 is `tnext 1 0 1 0` of row 0.
* `rows_mem`: if row 0 encloses `M(0,·)` and the checks pass, every row `i` encloses `M(i,·)`.
 -/

namespace RHTabCore0515
open RHBall0504 RHBallVec0504 RHRec2D0515

def ratBall (S : ℕ) (N : ℤ) (D : ℕ) : Ball := ((N * S) / (D : ℤ), 1)

lemma mem_ratBall {S : ℕ} (hS : 0 < S) (N : ℤ) {D : ℕ} (hD : 0 < D) :
    mem S ((N : ℝ) / D) (ratBall S N D) := by
  unfold mem ratBall
  simp only
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set q : ℤ := (N * S) / (D : ℤ)
  set r : ℤ := (N * S) % (D : ℤ)
  have hqr : N * S = (D : ℤ) * q + r := (Int.mul_ediv_add_emod _ _).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hD.ne')
  have hr1 : r < D := Int.emod_lt_of_pos _ (by exact_mod_cast hD)
  have hqr' : (N : ℝ) * S = D * q + r := by exact_mod_cast hqr
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℝ) < D := by exact_mod_cast hr1
  have e : (N : ℝ) / D - q / S = r / (D * S) := by
    field_simp
    linear_combination hqr'
  rw [e, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hS']
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hr1'.le hS'.le]

def chkAux (j : ℕ) (r0 : List Ball) : List (List Ball) → Bool
  | r1 :: r2 :: _ => r2 == tnext (2 * (j:ℤ) + 3) ((j:ℤ) + 1) (j + 2) 0 r1 (gz r1 0) r0
  | _ => true

/-- Structural recursion (kernel-reducible). -/
def chkFrom (j : ℕ) : List (List Ball) → Bool
  | [] => true
  | r0 :: rest => chkAux j r0 rest && chkFrom (j + 1) rest

def chk1 : List (List Ball) → Bool
  | r0 :: r1 :: _ => r1 == tnext 1 0 1 0 r0 (gz r0 0) r0
  | _ => true

lemma rowMem_nil (S : ℕ) (f : ℕ → ℝ) : RowMem S f [] := fun i hi => by simp at hi

theorem rows_from {S : ℕ} (hS : 0 < S) (w : ℝ → ℝ) (hw : IntervalIntegrable w MeasureTheory.volume (-1) 1) :
    ∀ (tab : List (List Ball)) (j : ℕ), chkFrom j tab = true →
      RowMem S (Mw w j) (tab.getD 0 []) → RowMem S (Mw w (j + 1)) (tab.getD 1 []) →
      ∀ i, RowMem S (Mw w (j + i)) (tab.getD i []) := by
  intro tab
  induction tab with
  | nil => intro j _ _ _ i; simpa using rowMem_nil S (Mw w (j + i))
  | cons r0 rest ih =>
    intro j hc h0 h1 i
    cases rest with
    | nil =>
      cases i with
      | zero => simpa using h0
      | succ i => simpa using rowMem_nil S (Mw w (j + (i + 1)))
    | cons r1 rest2 =>
      cases rest2 with
      | nil =>
        match i with
        | 0 => simpa using h0
        | 1 => simpa using h1
        | i + 2 => simpa using rowMem_nil S (Mw w (j + (i + 2)))
      | cons r2 rest3 =>
        rw [chkFrom, Bool.and_eq_true] at hc
        obtain ⟨ha, hc'⟩ := hc
        have hr2 : r2 = tnext (2 * (j:ℤ) + 3) ((j:ℤ) + 1) (j + 2) 0 r1 (gz r1 0) r0 := by
          simpa only [chkAux, beq_iff_eq] using ha
        have h0' : RowMem S (Mw w j) r0 := by simpa using h0
        have h1' : RowMem S (Mw w (j + 1)) r1 := by simpa using h1
        have h2 : RowMem S (Mw w (j + 2)) r2 := by rw [hr2]; exact row_step hS w hw j h1' h0'
        cases i with
        | zero => simpa using h0
        | succ i =>
          have := ih (j + 1) hc' (by simpa using h1') (by simpa using h2) i
          rw [show j + (i + 1) = j + 1 + i by omega]
          simpa using this

theorem rows_mem {S : ℕ} (hS : 0 < S) (w : ℝ → ℝ) (hw : IntervalIntegrable w MeasureTheory.volume (-1) 1)
    (tab : List (List Ball)) (hc1 : chk1 tab = true) (hc : chkFrom 0 tab = true)
    (h0 : RowMem S (Mw w 0) (tab.getD 0 [])) : ∀ i, RowMem S (Mw w i) (tab.getD i []) := by
  have h1 : RowMem S (Mw w 1) (tab.getD 1 []) := by
    match tab, hc1, h0 with
    | [], _, _ => exact rowMem_nil S _
    | [r0], _, _ => exact rowMem_nil S _
    | r0 :: r1 :: rest, hc1, h0 =>
      simp only [chk1, beq_iff_eq] at hc1
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 ⊢
      rw [hc1]; exact row_one hS w hw h0
  intro i
  simpa using rows_from hS w hw tab 0 hc h0 h1 i

end RHTabCore0515

