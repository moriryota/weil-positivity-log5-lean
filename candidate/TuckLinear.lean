import MathlibAll0483
import TuckMonomial

open Polynomial
open scoped BigOperators

namespace RHTuckLinear

noncomputable def operator : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  Polynomial.lsum (fun n => LinearMap.toSpanSingleton ℂ (Polynomial ℂ) (RHTuckMonomial.image n))

theorem operator_eq_sum (p : Polynomial ℂ) :
    operator p = ∑ n ∈ p.support, p.coeff n • RHTuckMonomial.image n := by
  have h : operator p
      = p.sum (fun n c => c • RHTuckMonomial.image n) := rfl
  rw [h, Polynomial.sum_def]

theorem coeff_above (p : Polynomial ℂ) (m : ℕ) (hm : p.natDegree < m) :
    (operator p).coeff m = 0 := by
  rw [operator_eq_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn' : n ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
  rw [Polynomial.coeff_smul, smul_eq_mul,
    RHTuckMonomial.coeff_above n m (by omega), mul_zero]

theorem coeff_diag (p : Polynomial ℂ) :
    (operator p).coeff p.natDegree
      = 2 * (harmonic p.natDegree : ℂ) * p.coeff p.natDegree := by
  rw [operator_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single p.natDegree]
  · rw [Polynomial.coeff_smul, smul_eq_mul, RHTuckMonomial.coeff_diag]
    ring
  · intro n hn hne
    have hn' : n ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
    rw [Polynomial.coeff_smul, smul_eq_mul,
      RHTuckMonomial.coeff_above n p.natDegree (lt_of_le_of_ne hn' hne), mul_zero]
  · intro hd
    rw [Polynomial.notMem_support_iff] at hd
    rw [Polynomial.coeff_smul, smul_eq_mul, hd, zero_mul]

/-- Auxiliary consequence of `coeff_above`: the operator does not raise degree. -/
theorem natDegree_operator_le (p : Polynomial ℂ) :
    (operator p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => coeff_above p N hN

end RHTuckLinear

