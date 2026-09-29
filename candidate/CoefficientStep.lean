import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# A binomial-coefficient product step lemma

`b n k = C(n,k) * C(n+k,n)`.  We prove the adjacent-`k` recurrence

`(k+1)^2 * b n (k+1) = (n-k) * (n+k+1) * b n k`   (for `k ≤ n`).

Everything is derived from three standard Mathlib identities:
`Nat.choose_succ_right_eq`, `Nat.choose_mul_succ_eq` and `Nat.choose_symm_add`.
-/

namespace RHCoefStep

/-- Product of binomial coefficients `C(n,k) * C(n+k,n)`. -/
def b (n k : ℕ) : ℕ := n.choose k * (n + k).choose n

/-- Adjacent-`k` recurrence for `b`. -/
theorem b_k_step (n k : ℕ) (hk : k ≤ n) :
    (k + 1) ^ 2 * b n (k + 1) = (n - k) * (n + k + 1) * b n k := by
  -- symmetry rewrites: `C(n+k, n) = C(n+k, k)` etc.
  have s1 : (n + k).choose n = (n + k).choose k := Nat.choose_symm_add
  have s2 : (n + (k + 1)).choose n = (n + (k + 1)).choose (k + 1) := Nat.choose_symm_add
  -- lower-index step for `C(n, ·)`
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
    Nat.choose_succ_right_eq n k
  -- lower-index step for `C(n+k+1, ·)`
  have h2 : (n + (k + 1)).choose (k + 1) * (k + 1)
      = (n + (k + 1)).choose k * (n + 1) := by
    have h := Nat.choose_succ_right_eq (n + (k + 1)) k
    rwa [show n + (k + 1) - k = n + 1 from by omega] at h
  -- upper-index step: `C(n+k, k) → C(n+k+1, k)`
  have h3 : (n + k).choose k * (n + k + 1)
      = (n + (k + 1)).choose k * (n + 1) := by
    have h := Nat.choose_mul_succ_eq (n + k) k
    rwa [show n + k + 1 - k = n + 1 from by omega] at h
  simp only [b]
  rw [s1, s2]
  calc
    (k + 1) ^ 2 * (n.choose (k + 1) * (n + (k + 1)).choose (k + 1))
        = (n.choose (k + 1) * (k + 1)) * ((n + (k + 1)).choose (k + 1) * (k + 1)) := by
          ring
    _ = (n.choose k * (n - k)) * ((n + (k + 1)).choose k * (n + 1)) := by rw [h1, h2]
    _ = (n.choose k * (n - k)) * ((n + k).choose k * (n + k + 1)) := by rw [← h3]
    _ = (n - k) * (n + k + 1) * (n.choose k * (n + k).choose k) := by ring

/-- `n`-direction step for `b` (the optional "slack" goal), from
`Nat.choose_mul_succ_eq` used twice. -/
theorem b_n_step (n k : ℕ) (hk : k ≤ n + 1) :
    (n + 1 - k) * b (n + 1) k = (n + k + 1) * b n k := by
  have symB : (n + 1 + k).choose (n + 1) = (n + 1 + k).choose k := Nat.choose_symm_add
  have symC : (n + k).choose n = (n + k).choose k := Nat.choose_symm_add
  have ha : (n + 1).choose k * (n + 1 - k) = n.choose k * (n + 1) :=
    (Nat.choose_mul_succ_eq n k).symm
  have hb : (n + k).choose k * (n + k + 1) = (n + k + 1).choose k * (n + 1) := by
    have h := Nat.choose_mul_succ_eq (n + k) k
    rwa [show n + k + 1 - k = n + 1 from by omega] at h
  have eqk : (n + 1 + k).choose k = (n + k + 1).choose k := by
    rw [show n + 1 + k = n + k + 1 from by omega]
  simp only [b]
  rw [symB, eqk, symC]
  calc
    (n + 1 - k) * ((n + 1).choose k * (n + k + 1).choose k)
        = ((n + 1).choose k * (n + 1 - k)) * (n + k + 1).choose k := by ring
    _ = (n.choose k * (n + 1)) * (n + k + 1).choose k := by rw [ha]
    _ = n.choose k * ((n + k + 1).choose k * (n + 1)) := by ring
    _ = n.choose k * ((n + k).choose k * (n + k + 1)) := by rw [← hb]
    _ = (n + k + 1) * (n.choose k * (n + k).choose k) := by ring

end RHCoefStep

