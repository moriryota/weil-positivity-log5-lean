import Sparse0504

/-! # 0505: iterated integrals and `(1+u)^m`-multiples of `P_n` as Legendre vectors

* `α n m`: `α n 0 = δ_n`, `α n (m+1) = ImS (α n m)`; `Im^[m] (p n) = evV (n+1+m) (α n m)`.
* `β n m`: `β n 0 = δ_n`, `β n (m+1) = β n m + XS (β n m)`; `(1+u)^m p n u = evV (n+1+m) (β n m) u`.
* `Im^[m] 1 = (1+u)^m/m!`, `Ip^[m] 1 = (1−u)^m/m!`. -/

open Finset
open scoped BigOperators

namespace RHIter0505
open RHLeg0503 RHCauchy0503 RHLegVec0503 RHSparse0504

noncomputable def δ (n : ℕ) (l : ℕ) : ℝ := if l = n then 1 else 0

noncomputable def α (n : ℕ) : ℕ → ℕ → ℝ
  | 0 => δ n
  | m + 1 => ImS (α n m)

noncomputable def β (n : ℕ) : ℕ → ℕ → ℝ
  | 0 => δ n
  | m + 1 => fun l => β n m l + XS (β n m) l

lemma ImS_zero {c : ℕ → ℝ} {N : ℕ} (hc : ∀ l, N ≤ l → c l = 0) : ∀ l, N + 1 ≤ l → ImS c l = 0
  | 0, h => by omega
  | l + 1, h => by simp only [ImS, Ar]; rw [hc l (by omega), hc (l + 2) (by omega)]; simp

lemma XS_zero {c : ℕ → ℝ} {N : ℕ} (hc : ∀ l, N ≤ l → c l = 0) : ∀ l, N + 1 ≤ l → XS c l = 0
  | 0, h => by omega
  | l + 1, h => by simp only [XS, Bx, Cx]; rw [hc l (by omega), hc (l + 2) (by omega)]; simp

lemma α_supp (n : ℕ) : ∀ m l, n + 1 + m ≤ l → α n m l = 0
  | 0, l, h => by simp [α, δ]; omega
  | m + 1, l, h => ImS_zero (α_supp n m) l (by omega)

lemma β_supp (n : ℕ) : ∀ m l, n + 1 + m ≤ l → β n m l = 0
  | 0, l, h => by simp [β, δ]; omega
  | m + 1, l, h => by
      simp only [β]; rw [β_supp n m l (by omega), XS_zero (β_supp n m) l (by omega)]; simp

lemma evV_extend {N : ℕ} {c : ℕ → ℝ} (hc : ∀ l, N ≤ l → c l = 0) (u : ℝ) :
    evV (N + 1) c u = evV N c u := by
  unfold evV; rw [sum_range_succ, hc N le_rfl]; simp

lemma p_eq_evV (n : ℕ) : p n = evV (n + 1) (δ n) := by
  funext u; unfold evV δ
  rw [sum_eq_single n (fun l _ hl => by simp [hl]) (fun h => by simp at h)]
  simp

theorem Im_iter_p (n : ℕ) : ∀ m, Im^[m] (p n) = evV (n + 1 + m) (α n m)
  | 0 => by simp [α, p_eq_evV]
  | m + 1 => by
      rw [Function.iterate_succ_apply', Im_iter_p n m, Im_evS (α_supp n m)]
      rfl

theorem onePlus_p (n : ℕ) : ∀ m (u : ℝ), (1 + u) ^ m * p n u = evV (n + 1 + m) (β n m) u
  | 0, u => by simp [β, p_eq_evV]
  | m + 1, u => by
      rw [pow_succ, mul_comm ((1 + u) ^ m) (1 + u), mul_assoc, onePlus_p n m u, add_mul, one_mul,
        X_evS (β_supp n m), ← evV_extend (β_supp n m) u]
      unfold evV
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun l _ => by simp only [β]; ring)

theorem Im_iter_one : ∀ (m : ℕ) (u : ℝ), (Im^[m] (fun _ => (1 : ℝ))) u = (1 + u) ^ m / m.factorial
  | 0, u => by show (1 : ℝ) = (1 + u) ^ 0 / (Nat.factorial 0 : ℝ); simp
  | m + 1, u => by
      rw [Function.iterate_succ_apply']
      have e : (Im^[m] fun _ => (1 : ℝ)) = fun v : ℝ => (1 + v) ^ m / (m.factorial : ℝ) := funext (Im_iter_one m)
      rw [e, Im]
      have h : ∀ v ∈ Set.uIcc (-1 : ℝ) u,
          HasDerivAt (fun v : ℝ => (1 + v) ^ (m + 1) / (m + 1).factorial) ((1 + v) ^ m / m.factorial) v := by
        intro v _
        have h1 := (((hasDerivAt_id' v).const_add 1).pow (m + 1)).div_const ((m + 1).factorial : ℝ)
        convert h1 using 1
        rw [Nat.add_sub_cancel, Nat.factorial_succ]; push_cast
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
        ((by fun_prop : Continuous fun v : ℝ => (1 + v) ^ m / m.factorial).intervalIntegrable _ _)]
      simp

theorem Ip_iter_one (m : ℕ) (u : ℝ) : (Ip^[m] (fun _ => (1 : ℝ))) u = (1 - u) ^ m / m.factorial := by
  rw [RHLegVec0503.Ip_iter, Im_iter_one]; ring_nf

end RHIter0505

