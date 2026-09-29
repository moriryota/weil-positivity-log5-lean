import ResidualCertificate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Matrix
open scoped BigOperators Matrix
namespace RHResidualCertificate
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite synthesis is bounded by the sum of squared column norms. -/
theorem synthesis_norm_sq_le (v : ι → E) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * (∑ i, (c i) ^ 2) := by
  have hn : ‖∑ i, c i • v i‖ ≤ ∑ i, |c i| * ‖v i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using
      norm_sum_le Finset.univ (fun i => c i • v i)
  have hs : 0 ≤ ∑ i, |c i| * ‖v i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hsq := (sq_le_sq₀ (norm_nonneg _) hs).2 hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |c i|) (fun i => ‖v i‖)
  exact hsq.trans (by simpa only [sq_abs, mul_comm] using hc)

noncomputable def transformedResidual (r : ι → E) (B : Matrix ι ι ℝ) (j : ι) : E :=
  ∑ i, B i j • r i

theorem residual_vector_mulVec (r : ι → E) (B : Matrix ι ι ℝ) (c : ι → ℝ) :
    residual_vector r (B *ᵥ c) = ∑ j, c j • transformedResidual r B j := by
  simp only [residual_vector, transformedResidual, mulVec, dotProduct,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm]

theorem transformed_gram (r : ι → E) (B : Matrix ι ι ℝ) :
    residual_gram_matrix (transformedResidual r B) =
      Bᵀ * residual_gram_matrix r * B := by
  ext j k
  simp only [residual_gram_matrix, transformedResidual, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem transformed_trace (r : ι → E) (B : Matrix ι ι ℝ) :
    Matrix.trace (Bᵀ * residual_gram_matrix r * B) =
      ∑ j, ‖transformedResidual r B j‖ ^ 2 := by
  rw [← transformed_gram]
  simp only [Matrix.trace, Matrix.diag, residual_gram_matrix,
    real_inner_self_eq_norm_sq]

theorem residual_bound_of_gram_trace (r : ι → E) (B : Matrix ι ι ℝ)
    (c : ι → ℝ) {dM τ s : ℝ} (hdM : 0 < dM)
    (htrace : Matrix.trace ((1 / dM) • (Bᵀ * residual_gram_matrix r * B)) ≤ τ)
    (hs : s = ∑ i, (c i)^2) :
    ‖residual_vector r (B *ᵥ c)‖ ^ 2 / dM ≤ τ * s := by
  rw [residual_vector_mulVec]
  have h := div_le_div_of_nonneg_right (synthesis_norm_sq_le (transformedResidual r B) c) hdM.le
  rw [Matrix.trace_smul, smul_eq_mul, transformed_trace] at htrace
  have hc : 0 ≤ ∑ i, (c i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ht := mul_le_mul_of_nonneg_right htrace hc
  rw [hs]
  calc
    _ ≤ ((∑ i, ‖transformedResidual r B i‖^2) * (∑ i, (c i)^2)) / dM := h
    _ = ((1 / dM) * (∑ i, ‖transformedResidual r B i‖^2)) * (∑ i, (c i)^2) := by ring
    _ ≤ _ := ht

/-- Supplies the residual input to Schur; hQ and hLow remain explicit. -/
theorem certificate_from_gram_trace (d_band v y : ι → ℝ)
    (hd : ∀ i, 0 < d_band i) (r : ι → E) (B : Matrix ι ι ℝ)
    (c : ι → ℝ) (z : E) {dM τ s η a Q : ℝ} (hdM : 0 < dM)
    (htrace : Matrix.trace ((1 / dM) • (Bᵀ * residual_gram_matrix r * B)) ≤ τ)
    (hs : s = ∑ i, (c i)^2)
    (hQ : a + (∑ i, (2 * v i * y i + d_band i * (y i)^2)) +
      2 * inner ℝ (residual_vector r (B *ᵥ c)) z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d_band i) :
    (1 - η - τ) * s ≤ Q := by
  exact RHWeightedSchur.certificate_lower_bound d_band v y hd
    (residual_vector r (B *ᵥ c)) z hdM hQ hLow
    (residual_bound_of_gram_trace r B c hdM htrace hs)
end RHResidualCertificate

