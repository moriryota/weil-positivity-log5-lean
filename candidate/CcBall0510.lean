import CcSs0510
import BallDot0509
import Coarse0509

/-! # 0510: ball evaluation of `ce N odd n` (Cc/Ss Taylor parts) for all `n`

`xB`: ball for `L/2`. `pw m ⊇ (L/2)^m`, `xiv m ⊇ ξ m` (via `vX`), accumulation over `m < N`:
`ceV S N odd xB ⊇ (n ↦ ce N odd n)`. -/

open Finset
open scoped BigOperators

namespace RHCcBall0510
open RHBall0504 RHBallVec0504 RHBallDot0509 RHSparse0504 RHIter0505 RHCcSs0510 RHLog5Bridge

def vscaleB (S : ℕ) (a : Ball) (bs : List Ball) : List Ball := bs.map (mulB S a)

lemma vecMem_vscaleB {S : ℕ} (hS : 0 < S) {x : ℝ} {a : Ball} {c : ℕ → ℝ} {bs : List Ball}
    (ha : mem S x a) (h : VecMem S c bs) : VecMem S (fun l => x * c l) (vscaleB S a bs) := by
  intro l
  by_cases hl : l < bs.length
  · have e : gz (vscaleB S a bs) l = mulB S a (gz bs l) := by
      unfold vscaleB gz
      rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl, List.getElem_map]
    rw [e]; exact mem_mulB hS ha (h l)
  · have e : gz (vscaleB S a bs) l = (0, 0) := gz_of_len _ _ (by simp [vscaleB]; omega)
    rw [e]; show mem S (x * c l) (0, 0)
    rw [zero_of_len hS h (by omega), mul_zero]; exact (mem_zero S hS).mpr rfl

def pw (S : ℕ) (xB : Ball) : ℕ → Ball
  | 0 => ((S : ℤ), 0)
  | m + 1 => mulB S (pw S xB m) xB

lemma pw_mem {S : ℕ} (hS : 0 < S) {x : ℝ} {xB : Ball} (hx : mem S x xB) : ∀ m, mem S (x ^ m) (pw S xB m)
  | 0 => by
      simp only [pw, pow_zero]; unfold mem
      have : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
      simp [this]
  | m + 1 => by rw [pow_succ]; exact mem_mulB hS (pw_mem hS hx m) hx

/-- Loop over `m`: `xi ⊇ ξ m`, `acc ⊇ Σ_{j<m} [par j] x^j/j! ξ j`. -/
def ceLoop (S : ℕ) (xB : Ball) (odd : Bool) : ℕ → ℕ → List Ball → List Ball → List Ball
  | 0, _, _, acc => acc
  | c + 1, m, xi, acc =>
      ceLoop S xB odd c (m + 1) (vX xi)
        (if m % 2 = (if odd then 1 else 0) then vadd acc (vscaleB S (smul 1 m.factorial (pw S xB m)) xi) else acc)

lemma ceLoop_mem {S : ℕ} (hS : 0 < S) {x : ℝ} {xB : Ball} (hx : mem S x xB) (odd : Bool) :
    ∀ (c m : ℕ) (xi acc : List Ball) (A : ℕ → ℝ), VecMem S (ξ m) xi → VecMem S A acc →
      VecMem S (fun l => A l + ∑ j ∈ range c, (if (m + j) % 2 = (if odd then 1 else 0) then
          x ^ (m + j) / (m + j).factorial else 0) * ξ (m + j) l) (ceLoop S xB odd c m xi acc)
  | 0, m, xi, acc, A, _, hA => by simpa [ceLoop] using hA
  | c + 1, m, xi, acc, A, hxi, hA => by
      have hxi' : VecMem S (ξ (m + 1)) (vX xi) := vecMem_vX hS hxi
      have hco : mem S (x ^ m / m.factorial) (smul 1 m.factorial (pw S xB m)) := by
        have := mem_smul hS 1 (d := m.factorial) (Nat.factorial_pos m) (pw_mem hS hx m)
        simpa using this
      simp only [ceLoop]
      have e : ∀ l, ∀ j ∈ range c, (if (m + (j + 1)) % 2 = (if odd then 1 else 0) then
          x ^ (m + (j + 1)) / (m + (j + 1)).factorial else 0) * ξ (m + (j + 1)) l =
          (if (m + 1 + j) % 2 = (if odd then 1 else 0) then
          x ^ (m + 1 + j) / (m + 1 + j).factorial else 0) * ξ (m + 1 + j) l := fun l j _ => by
        rw [show m + (j + 1) = m + 1 + j by ring]
      by_cases hp : m % 2 = (if odd then 1 else 0)
      · rw [if_pos hp]
        have hacc := vecMem_vadd hA (vecMem_vscaleB hS hco hxi)
        have ih := ceLoop_mem hS hx odd c (m + 1) _ _ _ hxi' hacc
        convert ih using 2 with l
        rw [sum_range_succ', sum_congr rfl (e l)]
        simp only [add_zero]
        rw [if_pos hp]; ring
      · rw [if_neg hp]
        have ih := ceLoop_mem hS hx odd c (m + 1) _ _ _ hxi' hA
        convert ih using 2 with l
        rw [sum_range_succ', sum_congr rfl (e l)]
        simp only [add_zero]
        rw [if_neg hp]; ring

def ceV (S N : ℕ) (xB : Ball) (odd : Bool) : List Ball :=
  mapI (fun n b => smul 2 (2 * n + 1) b) 0 (ceLoop S xB odd N 0 (vunit S 0) [])

theorem ceV_mem {S : ℕ} (hS : 0 < S) {xB : Ball} (hx : mem S (halfWidth / 2) xB) (N : ℕ) (odd : Bool) :
    VecMem S (ce N odd) (ceV S N xB odd) := by
  have h0 : VecMem S (fun _ => (0 : ℝ)) ([] : List Ball) := fun l => by simp [gz, mem]
  have hl := ceLoop_mem hS hx odd N 0 (vunit S 0) [] (fun _ => 0) (vecMem_vunit hS 0) h0
  refine vecMem_mapI hS _ hl (fun n hm => ?_) (fun n hn => ?_)
  · have := mem_smul hS 2 (d := 2 * n + 1) (by omega) hm
    convert this using 1
    unfold ce; simp only [zero_add]; push_cast
    rw [sum_mul, sum_div]; exact sum_congr rfl (fun j _ => by ring)
  · unfold ce; simp only [zero_add] at hn
    have : ∀ j ∈ range N, (if j % 2 = (if odd then 1 else 0) then (halfWidth / 2) ^ j / j.factorial else 0) *
        (2 / (2 * n + 1) * ξ j n) = (2 / (2 * n + 1)) * ((if j % 2 = (if odd then 1 else 0) then
        (halfWidth / 2) ^ j / j.factorial else 0) * ξ j n) := fun j _ => by ring
    rw [sum_congr rfl this, ← mul_sum, hn, mul_zero]

end RHCcBall0510

