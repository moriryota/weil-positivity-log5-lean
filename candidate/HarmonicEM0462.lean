import ReciprocalEM0461
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set intervalIntegral
namespace RHHarmonicEM0462

theorem trapezoid_harmonic (N n : ℕ) :
    trapezoid_sum (fun x : ℝ => 1/x) N n =
    (harmonic (N+n) : ℝ) - (harmonic N : ℝ) +
      (1/2 : ℝ) / N - (1/2 : ℝ) / (N+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [trapezoid_sum_succ, ih]
    simp only [Nat.add_succ, harmonic_succ, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast, Nat.cast_succ, Nat.cast_add, Nat.cast_one, Int.cast_natCast, smul_eq_mul]
    ring

theorem integral_reciprocal (N n : ℕ) (hN : 0 < N) :
    (∫ x : ℝ in (N : ℝ)..N+n, 1/x) = Real.log (N+n) - Real.log N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMn : (0 : ℝ) < N+n := add_pos_of_pos_of_nonneg hNr (Nat.cast_nonneg n)
  rw [integral_one_div_of_pos hNr hMn, Real.log_div (ne_of_gt hMn) (ne_of_gt hNr)]

/-- The exact EM identity before Bernoulli parity simplification or remainder estimates. -/
theorem harmonic_em (N n s : ℕ) (hN : 0 < N) :
    (harmonic (N+n) : ℝ) - (harmonic N : ℝ) +
      (1/2 : ℝ) / N - (1/2 : ℝ) / (N+n) =
    Real.log (N+n) - Real.log N +
      ∑ j ∈ Finset.range s, (-1 : ℝ)^j * saw (j+2) 0 *
        (iteratedDerivWithin (j+1) (fun x : ℝ => 1/x) (Ioi 0) (N+n) -
         iteratedDerivWithin (j+1) (fun x : ℝ => 1/x) (Ioi 0) N) +
      (-1 : ℝ)^s * ∫ x in (N : ℝ)..N+n,
        saw (s+1) x * iteratedDerivWithin (s+1) (fun x : ℝ => 1/x) (Ioi 0) x := by
  have h := RHReciprocalEM0461.reciprocal_em N n s hN
  rw [trapezoid_harmonic, integral_reciprocal N n hN] at h
  exact h
noncomputable def derivativeTerm (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^k * (k.factorial : ℝ) * x ^ (-1 - (k : ℤ))

noncomputable def boundaryCorrection (s : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range s, (-1 : ℝ)^j * saw (j+2) 0 * derivativeTerm (j+1) x

noncomputable def corrected (N s : ℕ) : ℝ :=
  (harmonic N : ℝ) - Real.log N - (1/2 : ℝ)/N - boundaryCorrection s N

theorem integral_derivativeTerm (N n k : ℕ) (hN : 0 < N) :
    (∫ x in (N : ℝ)..N+n,
      saw k x * iteratedDerivWithin k (fun x : ℝ => 1/x) (Ioi 0) x) =
    ∫ x in (N : ℝ)..N+n, saw k x * derivativeTerm k x := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg n))] at hx
  have hx0 : 0 < x := lt_of_lt_of_le hNr hx.1
  dsimp only
  rw [RHReciprocalEM0461.reciprocal_derivative k hx0]
  rfl

/-- Exact finite remainder identity; no remainder upper bound is assumed or concluded. -/
theorem corrected_difference (N n s : ℕ) (hN : 0 < N) :
    corrected (N+n) s - corrected N s =
      (-1 : ℝ)^s * ∫ x in (N : ℝ)..N+n, saw (s+1) x * derivativeTerm (s+1) x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < N+n := add_pos_of_pos_of_nonneg hNr (Nat.cast_nonneg n)
  have h := harmonic_em N n s hN
  simp_rw [RHReciprocalEM0461.reciprocal_derivative _ hMr,
    RHReciprocalEM0461.reciprocal_derivative _ hNr] at h
  rw [integral_derivativeTerm N n (s+1) hN] at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  change (harmonic (N+n) : ℝ) - (harmonic N : ℝ) +
      (1/2 : ℝ)/N - (1/2 : ℝ)/(N+n) =
    Real.log (N+n) - Real.log N +
      (boundaryCorrection s (N+n) - boundaryCorrection s N) +
      (-1 : ℝ)^s * ∫ x in (N : ℝ)..N+n, saw (s+1) x * derivativeTerm (s+1) x at h
  simp only [corrected, Nat.cast_add]
  linarith

end RHHarmonicEM0462

