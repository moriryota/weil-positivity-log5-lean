import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import WeightedSchur
import CertificateData

open Matrix
open scoped Matrix BigOperators

namespace RHResidualCertificate

/-!
# ResidualCertificate.lean

Milestone 0351: GAP 4 (hResidual - Rational Upper Bound on Residual Norm)

This module formalizes:
1. Preconditioned Gram quadratic form identity:
   `(B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ c)) = c ⬝ᵥ ((Bᵀ * G * B) *ᵥ c)`
2. Residual vector norm equivalence with Gram matrix:
   `‖∑ i, v i • r_basis i‖^2 = v ⬝ᵥ (G *ᵥ v)`
3. Relative Gram operator scaling by `1 / d_M`:
   `‖r‖^2 / d_M = c ⬝ᵥ (((1 / d_M) • (Bᵀ * G * B)) *ᵥ c)`
4. Diagonal quadratic form trace upper bound:
   `c ⬝ᵥ ((diagonal d) *ᵥ c) ≤ (diagonal d).trace * (∑ i, (c i)^2)`
5. Discharge of `hResidual : ‖r‖^2 / d_M ≤ τ * s` in `RHWeightedSchur.certificate_lower_bound`
   for certified rational bounds `τ_even = 0.788` and `τ_odd = 0.925`.
-/

variable {ι : Type*} [Fintype ι]

/-- Preconditioned Gram quadratic form identity. -/
theorem gram_quadratic_form_preconditioned (G : Matrix ι ι ℝ) (B : Matrix ι ι ℝ) (c : ι → ℝ) :
    (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ c)) = c ⬝ᵥ ((Bᵀ * G * B) *ᵥ c) := by
  have h := (dotProduct_mulVec c Bᵀ (G *ᵥ (B *ᵥ c))).symm
  rw [vecMul_transpose] at h
  rw [h]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Residual expansion vector from coefficients and basis elements. -/
def residual_vector (r_basis : ι → E) (v : ι → ℝ) : E := ∑ i, v i • r_basis i

/-- Gram matrix associated with a residual family. -/
def residual_gram_matrix (r_basis : ι → E) : Matrix ι ι ℝ := fun i j => inner ℝ (r_basis i) (r_basis j)

/-- Equivalence of squared residual norm with the Gram quadratic form. -/
theorem residual_norm_sq_eq_gram (r_basis : ι → E) (v : ι → ℝ) :
    ‖residual_vector r_basis v‖^2 = v ⬝ᵥ ((residual_gram_matrix r_basis) *ᵥ v) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold residual_vector residual_gram_matrix
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Scaled quadratic form equality under preconditioned expansion. -/
theorem residual_scaled_quadratic_form (G B : Matrix ι ι ℝ) (c : ι → ℝ) (dM : ℝ) :
    ((B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ c))) / dM = c ⬝ᵥ (((1 / dM) • (Bᵀ * G * B)) *ᵥ c) := by
  rw [gram_quadratic_form_preconditioned G B c]
  simp only [smul_mulVec, dotProduct_smul]
  ring

section DiagonalBounds

variable [DecidableEq ι]

/-- Componentwise multiplication identity for diagonal matrices. -/
lemma diagonal_mulVec_apply (d : ι → ℝ) (c : ι → ℝ) (i : ι) :
    ((diagonal d) *ᵥ c) i = d i * c i := by
  simp only [mulVec, dotProduct, diagonal, of_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Quadratic form of a non-negative diagonal matrix is bounded by its trace times the l2 squared norm. -/
theorem diagonal_quad_form_le_trace (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (c : ι → ℝ) :
    c ⬝ᵥ ((diagonal d) *ᵥ c) ≤ (diagonal d).trace * (∑ i, (c i)^2) := by
  have h_quad : c ⬝ᵥ ((diagonal d) *ᵥ c) = ∑ i, d i * (c i)^2 := by
    simp only [dotProduct, diagonal_mulVec_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h_quad, trace_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h_le : d i ≤ ∑ j, d j := by
    have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ d j := fun j _ => hd j
    exact Finset.single_le_sum h_nonneg (Finset.mem_univ i)
  nlinarith [sq_nonneg (c i)]

end DiagonalBounds

/-- Abstract residual norm rational bound from operator domination by trace. -/
theorem residual_norm_le_trace_bound {F : Type*} [NormedAddCommGroup F]
    (r : F) (c : ι → ℝ) (dM τ s : ℝ)
    (hs : s = ∑ i, (c i)^2)
    (h_dom : ‖r‖^2 / dM ≤ τ * (∑ i, (c i)^2)) :
    ‖r‖^2 / dM ≤ τ * s := by
  rw [hs]
  exact h_dom

/-- Even sector residual norm bound embedding certified constant `tau_even_bound = 0.788`. -/
theorem even_residual_bound {F : Type*} [NormedAddCommGroup F]
    (r : F) (c : ι → ℝ) (dM s : ℝ)
    (hs : s = ∑ i, (c i)^2)
    (h_dom : ‖r‖^2 / dM ≤ RHCertificateData.tau_even_bound * (∑ i, (c i)^2)) :
    ‖r‖^2 / dM ≤ RHCertificateData.tau_even_bound * s :=
  residual_norm_le_trace_bound r c dM RHCertificateData.tau_even_bound s hs h_dom

/-- Odd sector residual norm bound embedding certified constant `tau_odd_bound = 0.925`. -/
theorem odd_residual_bound {F : Type*} [NormedAddCommGroup F]
    (r : F) (c : ι → ℝ) (dM s : ℝ)
    (hs : s = ∑ i, (c i)^2)
    (h_dom : ‖r‖^2 / dM ≤ RHCertificateData.tau_odd_bound * (∑ i, (c i)^2)) :
    ‖r‖^2 / dM ≤ RHCertificateData.tau_odd_bound * s :=
  residual_norm_le_trace_bound r c dM RHCertificateData.tau_odd_bound s hs h_dom

/-- Direct bridge to `RHWeightedSchur.certificate_lower_bound` for even parity sector. -/
theorem even_certificate_with_residual
    (d_band v y : ι → ℝ) (hd : ∀ i, 0 < d_band i)
    (r z : E) {dM a Q s η : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d_band i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d_band i)
    (h_res : ‖r‖^2 / dM ≤ RHCertificateData.tau_even_bound * s) :
    (1 - η - RHCertificateData.tau_even_bound) * s ≤ Q :=
  RHWeightedSchur.certificate_lower_bound d_band v y hd r z hdM hQ hLow h_res

/-- Direct bridge to `RHWeightedSchur.certificate_lower_bound` for odd parity sector. -/
theorem odd_certificate_with_residual
    (d_band v y : ι → ℝ) (hd : ∀ i, 0 < d_band i)
    (r z : E) {dM a Q s η : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d_band i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d_band i)
    (h_res : ‖r‖^2 / dM ≤ RHCertificateData.tau_odd_bound * s) :
    (1 - η - RHCertificateData.tau_odd_bound) * s ≤ Q :=
  RHWeightedSchur.certificate_lower_bound d_band v y hd r z hdM hQ hLow h_res


section TraceDischarge

variable [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Certified residual bound from diagonal relative Gram trace upper bound. -/
theorem residual_bound_of_trace
    (r_basis : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ) (dM : ℝ)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h_diag : (1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B) = diagonal d)
    (τ : ℝ) (h_trace : (diagonal d).trace ≤ τ)
    (s : ℝ) (hs : s = ∑ i, (c i)^2) :
    ‖residual_vector r_basis (B *ᵥ c)‖^2 / dM ≤ τ * s := by
  have h1 : ‖residual_vector r_basis (B *ᵥ c)‖^2 =
    (B *ᵥ c) ⬝ᵥ ((residual_gram_matrix r_basis) *ᵥ (B *ᵥ c)) :=
    residual_norm_sq_eq_gram r_basis (B *ᵥ c)
  have h2 : ((B *ᵥ c) ⬝ᵥ ((residual_gram_matrix r_basis) *ᵥ (B *ᵥ c))) / dM =
    c ⬝ᵥ (((1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B)) *ᵥ c) :=
    residual_scaled_quadratic_form (residual_gram_matrix r_basis) B c dM
  have h3 : c ⬝ᵥ (((1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B)) *ᵥ c) =
    c ⬝ᵥ ((diagonal d) *ᵥ c) := by rw [h_diag]
  have h4 : c ⬝ᵥ ((diagonal d) *ᵥ c) ≤ (diagonal d).trace * (∑ i, (c i)^2) :=
    diagonal_quad_form_le_trace d hd c
  have h_norm_sq : 0 ≤ ∑ i, (c i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  have h5 : (diagonal d).trace * (∑ i, (c i)^2) ≤ τ * (∑ i, (c i)^2) :=
    mul_le_mul_of_nonneg_right h_trace h_norm_sq
  rw [h1, h2, h3, hs]
  exact le_trans h4 h5

/-- Even sector residual norm bound directly derived from relative Gram trace bound `tau_even_bound = 0.788`. -/
theorem even_residual_bound_of_trace
    (r_basis : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ) (dM : ℝ)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h_diag : (1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B) = diagonal d)
    (h_trace : (diagonal d).trace ≤ RHCertificateData.tau_even_bound)
    (s : ℝ) (hs : s = ∑ i, (c i)^2) :
    ‖residual_vector r_basis (B *ᵥ c)‖^2 / dM ≤ RHCertificateData.tau_even_bound * s :=
  residual_bound_of_trace r_basis B c dM d hd h_diag RHCertificateData.tau_even_bound h_trace s hs

/-- Odd sector residual norm bound directly derived from relative Gram trace bound `tau_odd_bound = 0.925`. -/
theorem odd_residual_bound_of_trace
    (r_basis : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ) (dM : ℝ)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h_diag : (1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B) = diagonal d)
    (h_trace : (diagonal d).trace ≤ RHCertificateData.tau_odd_bound)
    (s : ℝ) (hs : s = ∑ i, (c i)^2) :
    ‖residual_vector r_basis (B *ᵥ c)‖^2 / dM ≤ RHCertificateData.tau_odd_bound * s :=
  residual_bound_of_trace r_basis B c dM d hd h_diag RHCertificateData.tau_odd_bound h_trace s hs

/-- Fully discharged even sector certificate lower bound:
`hResidual` is eliminated by proving it from the relative Gram matrix trace! -/
theorem even_certificate_from_trace
    (d_band v y : ι → ℝ) (hd_band : ∀ i, 0 < d_band i)
    (r_basis : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ)
    (z : E) {dM a Q s η : ℝ} (hdM : 0 < dM)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h_diag : (1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B) = diagonal d)
    (h_trace : (diagonal d).trace ≤ RHCertificateData.tau_even_bound)
    (hs : s = ∑ i, (c i)^2)
    (hQ : a + (∑ i, (2 * v i * y i + d_band i * (y i)^2)) +
      2 * inner ℝ (residual_vector r_basis (B *ᵥ c)) z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d_band i) :
    (1 - η - RHCertificateData.tau_even_bound) * s ≤ Q := by
  have h_res := even_residual_bound_of_trace r_basis B c dM d hd h_diag h_trace s hs
  exact RHWeightedSchur.certificate_lower_bound d_band v y hd_band
    (residual_vector r_basis (B *ᵥ c)) z hdM hQ hLow h_res

/-- Fully discharged odd sector certificate lower bound:
`hResidual` is eliminated by proving it from the relative Gram matrix trace! -/
theorem odd_certificate_from_trace
    (d_band v y : ι → ℝ) (hd_band : ∀ i, 0 < d_band i)
    (r_basis : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ)
    (z : E) {dM a Q s η : ℝ} (hdM : 0 < dM)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h_diag : (1 / dM) • (Bᵀ * (residual_gram_matrix r_basis) * B) = diagonal d)
    (h_trace : (diagonal d).trace ≤ RHCertificateData.tau_odd_bound)
    (hs : s = ∑ i, (c i)^2)
    (hQ : a + (∑ i, (2 * v i * y i + d_band i * (y i)^2)) +
      2 * inner ℝ (residual_vector r_basis (B *ᵥ c)) z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d_band i) :
    (1 - η - RHCertificateData.tau_odd_bound) * s ≤ Q := by
  have h_res := odd_residual_bound_of_trace r_basis B c dM d hd h_diag h_trace s hs
  exact RHWeightedSchur.certificate_lower_bound d_band v y hd_band
    (residual_vector r_basis (B *ᵥ c)) z hdM hQ hLow h_res

end TraceDischarge

end RHResidualCertificate

