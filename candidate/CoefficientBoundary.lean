import InteriorCoefficient
namespace RHLegendreContract

theorem b_top_recurrence (n : ℕ) :
    ((n:ℝ)+2) * (b (n+2) (n+2):ℝ) = 2*(2*(n:ℝ)+3)*(b (n+1) (n+1):ℝ) := by
  have h1 := b_n_step (n+1) (n+1) (by omega)
  have h2 := RHCoefStep.b_k_step (n+2) (n+1) (by omega)
  have h1r : (b (n+2) (n+1):ℝ) = (2*(n:ℝ)+3)*(b (n+1) (n+1):ℝ) := by
    have h := congrArg (fun a : ℕ => (a:ℝ)) h1
    norm_num at h
    convert h using 1 <;> congr 1 <;> push_cast <;> ring
  have h2r : ((n:ℝ)+2)^2*(b (n+2) (n+2):ℝ) =
      (2*(n:ℝ)+4)*(b (n+2) (n+1):ℝ) := by
    change (n+1+1)^2 * b (n+2) (n+1+1) =
      (n+2-(n+1))*(n+2+(n+1)+1)*b (n+2) (n+1) at h2
    have h := congrArg (fun a : ℕ => (a:ℝ)) h2
    norm_num at h
    convert h using 1 <;> congr 1 <;> push_cast <;> ring
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [h1r] at h2r
  nlinarith [h2r]

theorem b_eq_zero_of_lt (n k : ℕ) (hk : n<k) : b n k=0 := by
  simp [b, Nat.choose_eq_zero_of_lt hk]

theorem b_recurrence_succ (n k : ℕ) :
    ((n:ℝ)+2)*(b (n+2) (k+1):ℝ) - (2*(n:ℝ)+3)*(b (n+1) (k+1):ℝ) -
      2*(2*(n:ℝ)+3)*(b (n+1) k:ℝ) + ((n:ℝ)+1)*(b n (k+1):ℝ)=0 := by
  by_cases hk : k≤n
  · exact b_interior_recurrence n k hk
  · by_cases he : k=n+1
    · subst k
      rw [b_eq_zero_of_lt (n+1) (n+1+1) (by omega), b_eq_zero_of_lt n (n+1+1) (by omega)]
      have h := b_top_recurrence n
      norm_num at *
      nlinarith [h]
    · rw [b_eq_zero_of_lt (n+2) (k+1) (by omega),
        b_eq_zero_of_lt (n+1) (k+1) (by omega),
        b_eq_zero_of_lt (n+1) k (by omega), b_eq_zero_of_lt n (k+1) (by omega)]
      norm_num
end RHLegendreContract
