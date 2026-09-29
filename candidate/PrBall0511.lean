import PrAff0511
import CcBall0510

/-! # 0511: ball algorithm for the affine Legendre vectors and their contraction

`afB S aB gB : ℕ → List Ball × List Ball` (pairs `(Af l, Af (l+1))`), `VecMem S (Af α γ l)`;
`dB S A B ⊇ Σ_j A_j B_j · 2/(2j+1)`. -/

open Finset
open scoped BigOperators

namespace RHPrBall0511
open RHBall0504 RHBallVec0504 RHBallDot0509 RHSparse0504 RHIter0505 RHPrAff0511 RHCcBall0510

def afNext (S : ℕ) (aB gB : Ball) (l : ℕ) (b1 b0 : List Ball) : List Ball :=
  vsub (vsmul (2 * (l : ℤ) + 3) (l + 2) (vadd (vscaleB S aB (vX b1)) (vscaleB S gB b1)))
    (vsmul ((l : ℤ) + 1) (l + 2) b0)

def af1 (S : ℕ) (aB gB : Ball) : List Ball := vadd (vscaleB S aB (vX (vunit S 0))) (vscaleB S gB (vunit S 0))

/-- List of the first `N` vectors `Af 0 .. Af (N−1)`. -/
def afList (S : ℕ) (aB gB : Ball) : ℕ → ℕ → List Ball → List Ball → List (List Ball)
  | 0, _, _, _ => []
  | c + 1, l, b0, b1 => b0 :: afList S aB gB c (l + 1) b1 (afNext S aB gB l b1 b0)

theorem afList_mem {S : ℕ} (hS : 0 < S) {α γ : ℝ} {aB gB : Ball} (ha : mem S α aB) (hg : mem S γ gB) :
    ∀ (c l : ℕ) (b0 b1 : List Ball), VecMem S (Af α γ l) b0 → VecMem S (Af α γ (l + 1)) b1 →
      ∀ j < c, VecMem S (Af α γ (l + j)) ((afList S aB gB c l b0 b1).getD j [])
  | 0, l, b0, b1, _, _, j, hj => absurd hj (by omega)
  | c + 1, l, b0, b1, h0, h1, 0, _ => by simpa [afList] using h0
  | c + 1, l, b0, b1, h0, h1, j + 1, hj => by
      simp only [afList, List.getD_cons_succ]
      have h2 : VecMem S (Af α γ (l + 2)) (afNext S aB gB l b1 b0) := by
        have t1 := vecMem_vsmul hS (2 * (l : ℤ) + 3) (d := l + 2) (by omega)
          (vecMem_vadd (vecMem_vscaleB hS ha (vecMem_vX hS h1)) (vecMem_vscaleB hS hg h1))
        have t0 := vecMem_vsmul hS ((l : ℤ) + 1) (d := l + 2) (by omega) h0
        have t := vecMem_vsub t1 t0
        have e : Af α γ (l + 2) = fun i => (α * XS (Af α γ (l + 1)) i + γ * Af α γ (l + 1) i) *
            ((2 * (l : ℤ) + 3 : ℤ) : ℝ) / ((l + 2 : ℕ) : ℝ) - Af α γ l i * (((l : ℤ) + 1 : ℤ) : ℝ) / ((l + 2 : ℕ) : ℝ) := by
          funext i; simp only [Af]; push_cast; ring
        rw [e]; exact t
      have ih := afList_mem hS ha hg c (l + 1) b1 _ h1 h2 j (by omega)
      rwa [show l + 1 + j = l + (j + 1) by ring] at ih

theorem af1_mem {S : ℕ} (hS : 0 < S) {α γ : ℝ} {aB gB : Ball} (ha : mem S α aB) (hg : mem S γ gB) :
    VecMem S (Af α γ 1) (af1 S aB gB) :=
  vecMem_vadd (vecMem_vscaleB hS ha (vecMem_vX hS (vecMem_vunit hS 0))) (vecMem_vscaleB hS hg (vecMem_vunit hS 0))

def afAll (S : ℕ) (aB gB : Ball) (N : ℕ) : List (List Ball) := afList S aB gB N 0 (vunit S 0) (af1 S aB gB)

theorem afAll_mem {S : ℕ} (hS : 0 < S) {α γ : ℝ} {aB gB : Ball} (ha : mem S α aB) (hg : mem S γ gB)
    (N l : ℕ) (hl : l < N) : VecMem S (Af α γ l) ((afAll S aB gB N).getD l []) := by
  have := afList_mem hS ha hg N 0 (vunit S 0) (af1 S aB gB) (vecMem_vunit hS 0) (af1_mem hS ha hg) l hl
  unfold afAll; simpa using this

/-- Weighted contraction `Σ_j A_j B_j 2/(2j+1)`. -/
def dB (S : ℕ) (A B : List Ball) : Ball := dotB S A (mapI (fun j b => smul 2 (2 * j + 1) b) 0 B)

theorem dB_mem {S : ℕ} (hS : 0 < S) {a b : ℕ → ℝ} {A B : List Ball} (hA : VecMem S a A) (hB : VecMem S b B)
    (N : ℕ) (hN : ∀ j, N ≤ j → a j = 0) :
    mem S (∑ j ∈ range N, a j * b j * (2 / (2 * j + 1))) (dB S A B) := by
  have hB' : VecMem S (fun j => b j * ((2 : ℤ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ)) (mapI (fun j b => smul 2 (2 * j + 1) b) 0 B) :=
    vecMem_mapI hS _ hB (fun j hm => mem_smul hS 2 (by omega) hm) (fun j hj => by simp [hj])
  have h := mem_dotB hS A _ a _ hA hB'
  have hAl : ∀ j, A.length ≤ j → a j = 0 := fun j hj => zero_of_len hS hA hj
  have hBl : ∀ j, (mapI (fun j b => smul 2 (2 * j + 1) b) 0 B).length ≤ j →
      b j * ((2 : ℤ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) = 0 := fun j hj => zero_of_len hS hB' hj
  set M := min A.length (mapI (fun j b => smul 2 (2 * j + 1) b) 0 B).length with hM
  set f : ℕ → ℝ := fun j => a j * (b j * ((2 : ℤ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ)) with hf
  have s1 : ∑ j ∈ range M, f j = ∑ j ∈ range (M + N), f j := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro j _ hj; simp at hj
    rcases min_le_iff.mp (show min A.length (mapI (fun j b => smul 2 (2 * j + 1) b) 0 B).length ≤ j from hj) with h1 | h1
    · simp only [hf]; rw [hAl j h1, zero_mul]
    · simp only [hf]; rw [hBl j h1, mul_zero]
  have s2 : ∑ j ∈ range N, f j = ∑ j ∈ range (M + N), f j := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro j _ hj; simp at hj
    simp only [hf]; rw [hN j hj, zero_mul]
  have key : ∑ j ∈ range N, f j = ∑ j ∈ range N, a j * b j * (2 / (2 * j + 1)) :=
    sum_congr rfl (fun j _ => by simp only [hf]; push_cast; ring)
  rw [← key, s2, ← s1]
  exact h

end RHPrBall0511

