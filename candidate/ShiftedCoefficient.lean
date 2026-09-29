import LegendreContract

open Polynomial

namespace RHLegendreContract

/-- Transfer of `Polynomial.coeff_shiftedLegendre` through the integer→real cast:
the `k`-th coefficient of `Q n` is `(-1)^k * C(n,k) * C(n+k,n)`. -/
theorem Q_coeff (n k : ℕ) :
    (Q n).coeff k
      = (-1 : ℝ) ^ k * (n.choose k : ℝ) * ((n + k).choose n : ℝ) := by
  rw [Q, coeff_map, coeff_shiftedLegendre, Int.coe_castRingHom]
  push_cast
  ring

/-- The combinatorial coefficient `b (n,k) = C(n,k) * C(n+k,n)` appearing in the
shifted Legendre polynomial `Q n` (see `Q_coeff`, up to the sign `(-1)^k`). -/
def b (n k : ℕ) : ℕ := n.choose k * (n + k).choose n

/-- A one-step (in `n`) adjacency identity for the coefficients `b`, valid for
`k ≤ n + 1`.  Stated over `ℕ` (the subtraction `n + 2 - k` is truncated
subtraction, harmless here since `k ≤ n + 1 ≤ n + 2`). -/
theorem b_adjacent (n k : ℕ) (hk : k ≤ n + 1) :
    (n + 2 - k) * b (n + 2) k = (n + k + 2) * b (n + 1) k := by
  have h1 : (n + 1).choose k * (n + 2) = (n + 2).choose k * (n + 2 - k) := by
    have h := Nat.choose_mul_succ_eq (n + 1) k
    simp only [show n + 1 + 1 = n + 2 from by omega] at h
    exact h
  have h2 : (n + 1 + k).choose k * (n + 2 + k) = (n + 2 + k).choose k * (n + 2) := by
    have h := Nat.choose_mul_succ_eq (n + 1 + k) k
    simp only [show n + 1 + k + 1 = n + 2 + k from by omega,
      show n + 2 + k - k = n + 2 from by omega] at h
    exact h
  have e2 : ((n + 2) + k).choose (n + 2) = ((n + 2) + k).choose k :=
    Nat.choose_symm_add
  have e1 : ((n + 1) + k).choose (n + 1) = ((n + 1) + k).choose k :=
    Nat.choose_symm_add
  unfold b
  rw [e2, e1]
  calc (n + 2 - k) * ((n + 2).choose k * ((n + 2) + k).choose k)
      = ((n + 2).choose k * (n + 2 - k)) * ((n + 2) + k).choose k := by ring
    _ = ((n + 1).choose k * (n + 2)) * ((n + 2) + k).choose k := by rw [← h1]
    _ = (n + 1).choose k * (((n + 2) + k).choose k * (n + 2)) := by ring
    _ = (n + 1).choose k * ((n + 1 + k).choose k * (n + 2 + k)) := by rw [← h2]
    _ = (n + k + 2) * ((n + 1).choose k * ((n + 1) + k).choose k) := by ring


end RHLegendreContract
