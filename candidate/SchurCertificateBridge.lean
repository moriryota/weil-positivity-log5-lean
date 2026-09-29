import CertificateData
import MatrixCertificateEnclosure
import WeightedSchur
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RHSchurCertificateBridge

open RHCertificateData RHMatrixCertificate

/-- Connection of SectorCertificate to the abstract WeightedSchur certificate lower bound.
When actual error parameters η, τ are bounded by the certificate:
1. (1 - η - τ) * s ≤ Q holds by abstract Schur completion of squares.
2. The certified margin bound cert.margin_bound * s ≤ Q holds whenever 0 ≤ s.
3. If s > 0, then 0 < Q (strict positivity). -/
theorem certified_sector_lower_bound
    (cert : SectorCertificate)
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_nonneg : 0 ≤ s)
    (hη : η ≤ cert.eta_bound)
    (hτ : τ ≤ cert.tau_bound) :
    cert.margin_bound * s ≤ Q := by
  have h_base := RHWeightedSchur.certificate_lower_bound d v y hd r z hdM hQ hLow hResidual
  have h_mult := certified_schur_margin_bound cert η τ hη hτ
  have h_le : cert.margin_bound * s ≤ (1 - η - τ) * s := mul_le_mul_of_nonneg_right h_mult hs_nonneg
  exact le_trans h_le h_base

/-- Strict positivity of the quadratic form from certified Schur margin when s > 0. -/
theorem certified_sector_strict_positivity
    (cert : SectorCertificate)
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_pos : 0 < s)
    (hη : η ≤ cert.eta_bound)
    (hτ : τ ≤ cert.tau_bound) :
    0 < Q := by
  have h_bound := certified_sector_lower_bound cert d v y hd r z hdM hQ hLow hResidual hs_pos.le hη hτ
  have h_pos_mult : 0 < cert.margin_bound * s := mul_pos cert.hmargin_pos hs_pos
  exact lt_of_lt_of_le h_pos_mult h_bound

/-- Specialization to the even parity sector. -/
theorem even_certified_schur_positivity
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_pos : 0 < s)
    (hη : η ≤ eta_even_bound)
    (hτ : τ ≤ tau_even_bound) :
    0 < Q :=
  certified_sector_strict_positivity even_sector_cert d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

/-- Specialization to the odd parity sector. -/
theorem odd_certified_schur_positivity
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_pos : 0 < s)
    (hη : η ≤ eta_odd_bound)
    (hτ : τ ≤ tau_odd_bound) :
    0 < Q :=
  certified_sector_strict_positivity odd_sector_cert d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

end RHSchurCertificateBridge

