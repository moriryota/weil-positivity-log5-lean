import LegendreContract
open Polynomial
namespace RHLegendreContract
noncomputable def rod (n : ℕ) : Polynomial ℝ := X^n * (1-X)^n

theorem rodrigues_real (n : ℕ) :
    (n.factorial : Polynomial ℝ) * Q n = derivative^[n] (rod n) := by
  have h := congrArg (fun p : Polynomial ℤ => p.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  simpa only [Polynomial.map_mul, Polynomial.map_natCast, ← Polynomial.iterate_derivative_map,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, Q, rod] using h

theorem eval_iterate_eq_zero_of_pow_dvd (F q : Polynomial ℝ) (n k : ℕ)
    (hdiv : q^n ∣ F) (hk : k<n) (a : ℝ) (ha : q.eval a=0) :
    (derivative^[k] F).eval a = 0 := by
  obtain ⟨R, hR⟩ := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k hdiv
  rw [hR, Polynomial.eval_mul, Polynomial.eval_pow, ha, zero_pow (Nat.sub_ne_zero_of_lt hk), zero_mul]

theorem rod_endpoint_zero (n k : ℕ) (hk : k<n) :
    (derivative^[k] (rod n)).eval 0 = 0 := by
  apply eval_iterate_eq_zero_of_pow_dvd (rod n) X n k
  · exact dvd_mul_right _ _
  · exact hk
  · simp

theorem rod_endpoint_one (n k : ℕ) (hk : k<n) :
    (derivative^[k] (rod n)).eval 1 = 0 := by
  apply eval_iterate_eq_zero_of_pow_dvd (rod n) (1-X) n k
  · exact dvd_mul_left _ _
  · exact hk
  · simp
end RHLegendreContract
