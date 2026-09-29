import Leg0503

namespace RHLegendreBound0520
open RHLeg0503

/-- A discrete energy identity obtained from the existing two derivative identities. -/
lemma energy_step (n : ℕ) (x : ℝ) :
    ((n:ℝ)+1)^2 * (p (n+1) x)^2 + (1-x^2)*(d (n+1) x)^2 =
    ((n:ℝ)+1)^2 * (p n x)^2 + (1-x^2)*(d n x)^2 := by
  obtain ⟨ha,hb⟩ := legS x n
  have hd : d n x = x*d (n+1) x - ((n:ℝ)+1)*p (n+1) x := by linarith
  have hp : ((n:ℝ)+1)*p n x = x*((n:ℝ)+1)*p (n+1) x + (1-x^2)*d (n+1) x := by nlinarith only [hb]
  have hs := congrArg (fun y : ℝ => y^2) hp
  rw [hd]
  nlinarith only [hs]

lemma energy_bound (x : ℝ) (hx : |x| ≤ 1) : ∀ n : ℕ,
    (p n x)^2 ≤ 1 ∧ (n:ℝ)^2 * (p n x)^2 + (1-x^2)*(d n x)^2 ≤ (n:ℝ)^2
  | 0 => by simp [p_zero, d_zero]
  | n+1 => by
    obtain ⟨hp,he⟩ := energy_bound x hx n
    have hv : 0 ≤ 1-x^2 := by nlinarith [sq_abs x, (abs_nonneg x)]
    have hk : 0 < ((n:ℝ)+1)^2 := by positivity
    have hinc : 0 ≤ 2*(n:ℝ)+1 := by positivity
    have hi := mul_le_mul_of_nonneg_left hp hinc
    have en := energy_step n x
    have he' : ((n:ℝ)+1)^2 * (p (n+1) x)^2 + (1-x^2)*(d (n+1) x)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith only [en,he,hi]
    have hz := mul_nonneg hv (sq_nonneg (d (n+1) x))
    constructor
    · nlinarith only [he',hz,hk]
    · simpa only [Nat.cast_add, Nat.cast_one] using he'

theorem abs_p_le_one (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |p n x| ≤ 1 := by
  have h := (energy_bound x hx n).1
  nlinarith [sq_abs (p n x), abs_nonneg (p n x)]
end RHLegendreBound0520
