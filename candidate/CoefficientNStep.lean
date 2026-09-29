import ShiftedCoefficient
open Polynomial
namespace RHLegendreContract

theorem b_n_step (n k : ℕ) (hk : k≤n+1) :
    (n+1-k) * b (n+1) k = (n+k+1) * b n k := by
  cases n with
  | zero =>
    have : k=0 ∨ k=1 := by omega
    rcases this with rfl | rfl <;> norm_num [b]
  | succ n =>
    by_cases h : k ≤ n+1
    · convert b_adjacent n k h using 1 <;> congr 1 <;> omega
    · have he : k=n+2 := by omega
      subst k
      simp [b, Nat.succ_eq_add_one, Nat.add_assoc, Nat.choose_eq_zero_of_lt (by omega : n+1<n+2)]
end RHLegendreContract
