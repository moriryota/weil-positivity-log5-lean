import Interval.EulerMaclaurin.EulerMaclaurin
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Tactic

open Set intervalIntegral
namespace RHReciprocalEM0461

theorem reciprocal_smooth (k : ℕ) :
    ContDiffOn ℝ k (fun x : ℝ => 1 / x) (Ioi 0) := by
  simpa only [one_div] using (contDiffOn_inv (𝕜 := ℝ) (n := k)).mono
    (show Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun x hx => by simpa using ne_of_gt hx)

theorem reciprocal_em (N n s : ℕ) (hN : 0 < N) :
    trapezoid_sum (fun x : ℝ => 1 / x) N n =
      (∫ x in (N : ℝ)..N + n, 1 / x) +
      ∑ j ∈ Finset.range s, (-1 : ℝ)^j * saw (j+2) 0 *
        (iteratedDerivWithin (j+1) (fun x : ℝ => 1/x) (Ioi 0) (N+n) -
         iteratedDerivWithin (j+1) (fun x : ℝ => 1/x) (Ioi 0) N) +
      (-1 : ℝ)^s * ∫ x in (N : ℝ)..N+n,
        saw (s+1) x * iteratedDerivWithin (s+1) (fun x : ℝ => 1/x) (Ioi 0) x := by
  have hb : Icc ((N : ℤ) : ℝ) ((N : ℤ) + n) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le (by exact_mod_cast hN) hx.1
  simpa only [Int.cast_natCast, smul_eq_mul, mul_assoc] using
    (trapezoid_sum_eq_integral_add (a := (N : ℤ)) (n := n)
      (reciprocal_smooth (s+1)) (uniqueDiffOn_Ioi 0) hb)

theorem reciprocal_derivative (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDerivWithin k (fun y : ℝ => 1/y) (Ioi 0) x =
      (-1 : ℝ)^k * (k.factorial : ℝ) * x ^ (-1 - (k : ℤ)) :=
  iteratedDerivWithin_one_div k isOpen_Ioi hx
end RHReciprocalEM0461
