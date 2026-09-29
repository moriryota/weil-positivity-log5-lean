import LegVec0503

/-! # 0504: sparse (neighbour) form of the Legendre vector operations

With `Ar c l = c_l/(2l+1)`:
* `ImS c 0 = Ar 0 − Ar 1`, `ImS c (m+1) = Ar m − Ar (m+2)`;
* `XS c m = [m ≥ 1]·(m/(2m−1))·c_{m−1} + ((m+1)/(2m+3))·c_{m+1}`
  (written as `Bx c (m−1) + Cx c (m+1)`, `Bx c l = (l+1)/(2l+1) c_l`, `Cx c l = l/(2l+1) c_l`).
If `c_l = 0` for `l ≥ N`: `Im (evV N c) = evV (N+1) (ImS c)` and `u·evV N c u = evV (N+1) (XS c) u`.
 -/

open Finset
open scoped BigOperators

namespace RHSparse0504
open RHLeg0503 RHCauchy0503 RHLegVec0503

noncomputable def Ar (c : ℕ → ℝ) (l : ℕ) : ℝ := c l / (2 * l + 1)
noncomputable def ImS (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => Ar c 0 - Ar c 1
  | m + 1 => Ar c m - Ar c (m + 2)

noncomputable def Bx (c : ℕ → ℝ) (l : ℕ) : ℝ := ((l : ℝ) + 1) / (2 * l + 1) * c l
noncomputable def Cx (c : ℕ → ℝ) (l : ℕ) : ℝ := (l : ℝ) / (2 * l + 1) * c l
noncomputable def XS (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => Cx c 1
  | m + 1 => Bx c m + Cx c (m + 2)

lemma eI_lt {l m : ℕ} (h : l + 1 < m) : eI l m = 0 := by
  cases l with
  | zero => simp only [eI]; split_ifs <;> first | omega | simp
  | succ k => simp only [eI]; split_ifs <;> first | omega | simp

lemma eI_gt {l m : ℕ} (h : m + 1 < l) : eI l m = 0 := by
  cases l with
  | zero => omega
  | succ k => simp only [eI]; split_ifs <;> first | omega | simp

lemma eX_lt {l m : ℕ} (h : l + 1 < m) : eX l m = 0 := by
  cases l with
  | zero => simp [eX]; omega
  | succ k => simp only [eX]; split_ifs <;> first | omega | simp

lemma eX_gt {l m : ℕ} (h : m + 1 < l) : eX l m = 0 := by
  cases l with
  | zero => omega
  | succ k => simp only [eX]; split_ifs <;> first | omega | simp

lemma eI_up (k : ℕ) : eI (k + 1) (k + 2) = 1 / (2 * (k : ℝ) + 3) := by
  simp only [eI]; split_ifs <;> first | omega | simp
lemma eI_down (k : ℕ) : eI (k + 1) k = -(1 / (2 * (k : ℝ) + 3)) := by
  simp only [eI]; split_ifs <;> first | omega | simp
lemma eI_diag (k : ℕ) : eI (k + 1) (k + 1) = 0 := by
  simp only [eI]; split_ifs <;> first | omega | simp
lemma eX_up (k : ℕ) : eX (k + 1) (k + 2) = ((k : ℝ) + 2) / (2 * k + 3) := by
  simp only [eX]; split_ifs <;> first | omega | simp
lemma eX_down (k : ℕ) : eX (k + 1) k = ((k : ℝ) + 1) / (2 * k + 3) := by
  simp only [eX]; split_ifs <;> first | omega | simp
lemma eX_diag (k : ℕ) : eX (k + 1) (k + 1) = 0 := by
  simp only [eX]; split_ifs <;> first | omega | simp

/-- Reduce a sparse coefficient sum to the window `l < m + 2`. -/
lemma window {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (e : ℕ → ℕ → ℝ)
    (he : ∀ l m, m + 1 < l → e l m = 0) (m : ℕ) :
    ∑ l ∈ range N, c l * e l m = ∑ l ∈ range (m + 2), c l * e l m := by
  have h1 : ∑ l ∈ range N, c l * e l m = ∑ l ∈ range (N + m + 2), c l * e l m := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro l hl hl'
    simp at hl hl'
    rw [hc l hl', zero_mul]
  have h2 : ∑ l ∈ range (m + 2), c l * e l m = ∑ l ∈ range (N + m + 2), c l * e l m := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro l hl hl'
    simp at hl hl'
    rw [he l m (by omega), mul_zero]
  rw [h1, h2]

lemma low_zero (c : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (he : ∀ l m, l + 1 < m → e l m = 0) (m : ℕ) :
    ∑ l ∈ range m, c l * e l (m + 1) = 0 :=
  sum_eq_zero (fun l hl => by simp at hl; rw [he l (m + 1) (by omega), mul_zero])

theorem ImV_eq {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (m : ℕ) :
    ImV N c m = ImS c m := by
  unfold ImV
  rw [window hc eI (fun l m h => eI_gt h)]
  cases m with
  | zero => simp [sum_range_succ, eI, ImS, Ar]; ring
  | succ m =>
      rw [sum_range_succ, sum_range_succ, sum_range_succ, low_zero c eI (fun l m h => eI_lt h)]
      cases m with
      | zero => simp [eI, ImS, Ar]; ring
      | succ k =>
          rw [show k + 1 + 1 = k + 2 from rfl, eI_up k, eI_diag (k + 1),
            show k + 1 + 2 = (k + 2) + 1 from rfl, eI_down (k + 2)]
          simp only [ImS, Ar]; push_cast; ring

theorem XV_eq {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (m : ℕ) :
    XV N c m = XS c m := by
  unfold XV
  rw [window hc eX (fun l m h => eX_gt h)]
  cases m with
  | zero => simp [sum_range_succ, eX, XS, Cx]; ring
  | succ m =>
      rw [sum_range_succ, sum_range_succ, sum_range_succ, low_zero c eX (fun l m h => eX_lt h)]
      cases m with
      | zero => simp [eX, XS, Bx, Cx]; ring
      | succ k =>
          rw [show k + 1 + 1 = k + 2 from rfl, eX_up k, eX_diag (k + 1),
            show k + 1 + 2 = (k + 2) + 1 from rfl, eX_down (k + 2)]
          simp only [XS, Bx, Cx]; push_cast; ring

lemma evV_congr {N : ℕ} {c d : ℕ → ℝ} (h : ∀ m < N, c m = d m) (u : ℝ) : evV N c u = evV N d u :=
  sum_congr rfl (fun m hm => by rw [h m (by simpa using hm)])

theorem Im_evS {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) :
    Im (evV N c) = evV (N + 1) (ImS c) := by
  rw [Im_evV]; funext u; exact evV_congr (fun m _ => ImV_eq hc m) u

theorem X_evS {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (u : ℝ) :
    u * evV N c u = evV (N + 1) (XS c) u := by
  rw [X_evV]; exact evV_congr (fun m _ => XV_eq hc m) u

end RHSparse0504

