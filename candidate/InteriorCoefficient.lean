import CoefficientNStep
import CoefficientStep
import RecurrenceAlgebra
namespace RHLegendreContract

theorem b_interior_recurrence (n k : ℕ) (hk : k≤n) :
    ((n:ℝ)+2)*(b (n+2) (k+1):ℝ) - (2*(n:ℝ)+3)*(b (n+1) (k+1):ℝ) -
      2*(2*(n:ℝ)+3)*(b (n+1) k:ℝ) + ((n:ℝ)+1)*(b n (k+1):ℝ)=0 := by
  have h1 := b_n_step (n+1) (k+1) (by omega)
  have h2 := b_n_step n (k+1) (by omega)
  have h3 := RHCoefStep.b_k_step (n+1) k (by omega)
  have h1r : ((n:ℝ)+1-k)*(b (n+2) (k+1):ℝ) = ((n:ℝ)+k+3)*(b (n+1) (k+1):ℝ) := by
    have h := congrArg (fun x : ℕ => (x:ℝ)) h1
    push_cast [Nat.cast_sub (by omega : k+1≤n+1+1), Nat.cast_sub (by omega : k≤n+1)] at h
    convert h using 1 <;> congr 1 <;> push_cast <;> ring
  have h2r : ((n:ℝ)-k)*(b (n+1) (k+1):ℝ) = ((n:ℝ)+k+2)*(b n (k+1):ℝ) := by
    have h := congrArg (fun x : ℕ => (x:ℝ)) h2
    push_cast [Nat.cast_sub (by omega : k+1≤n+1), Nat.cast_sub hk] at h
    convert h using 1 <;> congr 1 <;> ring
  have h3r : ((k:ℝ)+1)^2*(b (n+1) (k+1):ℝ) =
      ((n:ℝ)+1-k)*((n:ℝ)+k+2)*(b (n+1) k:ℝ) := by
    change (k+1)^2 * b (n+1) (k+1) = (n+1-k)*(n+1+k+1)*b (n+1) k at h3
    have h := congrArg (fun x : ℕ => (x:ℝ)) h3
    push_cast [Nat.cast_sub (by omega : k≤n+1)] at h
    convert h using 1 <;> ring

  apply RHRecurrenceAlgebra.interior_certificate (n:ℝ) (k:ℝ) _ _ _ _ _ _ h1r h2r h3r
  · have h : (k:ℝ)≤n := by exact_mod_cast hk
    linarith
  · positivity
end RHLegendreContract
