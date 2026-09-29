import ConditionalLog5
import ConcreteParameters
import CertificateData
import MatrixCertificateEnclosure
import StepB1_CertData
import ResidualTraceBound

open scoped Matrix BigOperators

namespace RHStepB2G6

open RHConditionalLog5 RHCertificateData RHConcreteParameters RHStepB1CertData RHResidualCertificate

/-- Algebraic reduction: the preconditioned residual Gram matrix trace equals the scaled sum
    of squared norms of the transformed column residuals. -/
theorem trace_smul_transformed_trace (o : Bool) :
    Matrix.trace ((1 / dM o) • ((concrete.B o)ᵀ * residual_gram_matrix (columnResidual o) * concrete.B o)) =
      (1 / dM o) * ∑ j : I, ‖transformedResidual (columnResidual o) (concrete.B o) j‖^2 := by
  rw [Matrix.trace_smul, smul_eq_mul, transformed_trace]

/-- The raw Arb trace enclosure hypothesis for concrete parameters:
    the scaled residual Gram trace is bounded by the certified raw Arb bounds. -/
def G6RawBound : Prop :=
  (Matrix.trace ((1 / dM false) • ((concrete.B false)ᵀ * residual_gram_matrix (columnResidual false) * concrete.B false)) ≤ even_tau_raw_upper) ∧
  (Matrix.trace ((1 / dM true) • ((concrete.B true)ᵀ * residual_gram_matrix (columnResidual true) * concrete.B true)) ≤ odd_tau_raw_upper)

/-- G6 transfer theorem: the raw Arb trace bound together with the certified rational bounds
    `even_tau_le_bound` and `odd_tau_le_bound` strictly implies G6 for concrete parameters. -/
theorem g6_of_raw_bound (h : G6RawBound) : G6 concrete := by
  intro o
  cases o
  · dsimp [G6, tau]
    exact h.1.trans even_tau_le_bound
  · dsimp [G6, tau]
    exact h.2.trans odd_tau_le_bound

/-- Transformed residual norm formulation of G6RawBound. -/
def G6NormBound : Prop :=
  ((1 / dM false) * (∑ j : I, ‖transformedResidual (columnResidual false) (concrete.B false) j‖^2) ≤ even_tau_raw_upper) ∧
  ((1 / dM true) * (∑ j : I, ‖transformedResidual (columnResidual true) (concrete.B true) j‖^2) ≤ odd_tau_raw_upper)

/-- Equivalence between matrix trace bound and transformed residual norm sum bound. -/
theorem g6_norm_bound_iff : G6NormBound ↔ G6RawBound := by
  unfold G6NormBound G6RawBound
  rw [trace_smul_transformed_trace false, trace_smul_transformed_trace true]

/-- G6 transfer directly from transformed residual norm sum bound. -/
theorem g6_of_norm_bound (h : G6NormBound) : G6 concrete :=
  g6_of_raw_bound (g6_norm_bound_iff.mp h)

end RHStepB2G6

