import CertificateData
import MatrixCertificateEnclosure
import SchurCertificateBridge
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace RHLeanCertificate

open RHCertificateData RHMatrixCertificate RHSchurCertificateBridge

/-- Parity sector selector for the numerical certificate. -/
inductive SectorParity
  | even
  | odd

/-- Canonical map from SectorParity to the verified SectorCertificate. -/
noncomputable def certificate_of_parity : SectorParity → SectorCertificate
  | SectorParity.even => even_sector_cert
  | SectorParity.odd => odd_sector_cert

/-- Certified Schur margin validity across both parity sectors:
Every sector certificate satisfies eta + tau < 1. -/
theorem lean_certificate_valid (p : SectorParity) :
    (certificate_of_parity p).eta_bound + (certificate_of_parity p).tau_bound < 1 := by
  cases p with
  | even => exact even_schur_margin
  | odd => exact odd_schur_margin

/-- Strict positivity of the certificate margin across both sectors. -/
theorem lean_certificate_margin_pos (p : SectorParity) :
    0 < (certificate_of_parity p).margin_bound := by
  cases p with
  | even => exact even_margin_pos
  | odd => exact odd_margin_pos

/-- Unified Lean certificate strict positivity theorem:
For either parity sector (even or odd), given the low-block and residual bounds
certified by the numerical certificate, whenever the low-degree component is active (s > 0),
the full quadratic form is strictly positive: 0 < Q. -/
theorem lean_certificate_positivity
    (p : SectorParity)
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_pos : 0 < s)
    (hη : η ≤ (certificate_of_parity p).eta_bound)
    (hτ : τ ≤ (certificate_of_parity p).tau_bound) :
    0 < Q := by
  cases p with
  | even =>
    exact even_certified_schur_positivity d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ
  | odd =>
    exact odd_certified_schur_positivity d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

/-- Unified lower bound on the quadratic form by the certified margin:
cert.margin_bound * s ≤ Q holds whenever s ≥ 0. -/
theorem lean_certificate_lower_bound
    (p : SectorParity)
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_nonneg : 0 ≤ s)
    (hη : η ≤ (certificate_of_parity p).eta_bound)
    (hτ : τ ≤ (certificate_of_parity p).tau_bound) :
    (certificate_of_parity p).margin_bound * s ≤ Q := by
  cases p with
  | even =>
    exact certified_sector_lower_bound even_sector_cert d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ
  | odd =>
    exact certified_sector_lower_bound odd_sector_cert d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ

end RHLeanCertificate

