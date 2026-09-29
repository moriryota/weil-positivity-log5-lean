import WeightedSchur
import CertificateData
import LeanCertificateIntegration
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

/-!
# LowCertificate.lean

Milestone 0350: GAP 3 (hLow - Low-Frequency Schur Complement Certificate Embedding)

This module formalizes:
1. The intermediate band Schur complement completion inequality:
   `a - ∑ i, (v i)^2 / d i ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`.
2. The low-frequency Schur operator lower bound embedding `(1 - η) * s ≤ a - ∑ i, (v i)^2 / d i`.
3. Strict positivity of the low-frequency Schur complement for both even and odd parity sectors.
4. Sector-specific and unified operator enclosure theorems binding certified numerical parameters
   (`eta_even_bound`, `eta_odd_bound`, `margin_even_bound`, `margin_odd_bound`) from `CertificateData`
   and `LeanCertificateIntegration`.
-/

namespace RHLowCertificate

open scoped BigOperators
open RHCertificateData RHLeanCertificate

/-!
### 1. The Intermediate Band Schur Complement Inequality
-/

/-- Intermediate band completion of squares:
For any low-block value `a`, coupling vector `v`, and intermediate state `y` with positive weights `d`,
the completed square sum is lower bounded by the Schur complement:
`a - ∑ i, (v i)^2 / d i ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`. -/
theorem intermediate_band_schur_bound {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i) (a : ℝ) :
    a - ∑ i, (v i)^2 / d i ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2) := by
  have hfin : - ∑ i, (v i)^2 / d i ≤ ∑ i, (2 * v i * y i + d i * (y i)^2) := by
    have h_terms := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => RHWeightedSchur.scalar_completion (hd i) (v := v i) (y := y i))
    rw [Finset.sum_neg_distrib] at h_terms
    exact h_terms
  linarith

/-- Embedding of the low-frequency Schur condition `(1 - η) * s ≤ a - ∑ i, (v i)^2 / d i`
into the intermediate band expansion:
`(1 - η) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`. -/
theorem hlow_operator_bound {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i) :
    (1 - η) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2) :=
  le_trans hLow (intermediate_band_schur_bound d v y hd a)

/-- Whenever the low-frequency energy `s` is strictly positive and `η < 1`,
the low-frequency Schur complement is strictly positive. -/
theorem hlow_positivity_of_active {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (d : ι → ℝ) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η < 1) (hs : 0 < s) :
    0 < a - ∑ i, (v i)^2 / d i := by
  have h_pos : 0 < (1 - η) * s := mul_pos (by linarith) hs
  exact lt_of_lt_of_le h_pos hLow

/-!
### 2. Even Sector Certified Schur Complement Bounds
-/

/-- The certified error bound for the even sector satisfies `eta_even_bound < 1`. -/
theorem eta_even_lt_one : eta_even_bound < 1 := by
  unfold eta_even_bound; norm_num

/-- Certified low-frequency Schur bound for the even sector:
`(1 - eta_even_bound) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`. -/
theorem even_hlow_schur_bound {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ eta_even_bound) (hs : 0 ≤ s) :
    (1 - eta_even_bound) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2) := by
  have h_embed := hlow_operator_bound d v y hd a s η hLow
  have h_mono : (1 - eta_even_bound) * s ≤ (1 - η) * s := by
    nlinarith
  exact le_trans h_mono h_embed

/-- Strict positivity of the low-frequency Schur complement in the even sector when `s > 0`. -/
theorem even_hlow_strictly_positive {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (d : ι → ℝ) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ eta_even_bound) (hs : 0 < s) :
    0 < a - ∑ i, (v i)^2 / d i := by
  have h_eta_lt : η < 1 := lt_of_le_of_lt hη eta_even_lt_one
  exact hlow_positivity_of_active v d a s η hLow h_eta_lt hs

/-!
### 3. Odd Sector Certified Schur Complement Bounds
-/

/-- The certified error bound for the odd sector satisfies `eta_odd_bound < 1`. -/
theorem eta_odd_lt_one : eta_odd_bound < 1 := by
  unfold eta_odd_bound; norm_num

/-- Certified low-frequency Schur bound for the odd sector:
`(1 - eta_odd_bound) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`. -/
theorem odd_hlow_schur_bound {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ eta_odd_bound) (hs : 0 ≤ s) :
    (1 - eta_odd_bound) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2) := by
  have h_embed := hlow_operator_bound d v y hd a s η hLow
  have h_mono : (1 - eta_odd_bound) * s ≤ (1 - η) * s := by
    nlinarith
  exact le_trans h_mono h_embed

/-- Strict positivity of the low-frequency Schur complement in the odd sector when `s > 0`. -/
theorem odd_hlow_strictly_positive {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (d : ι → ℝ) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ eta_odd_bound) (hs : 0 < s) :
    0 < a - ∑ i, (v i)^2 / d i := by
  have h_eta_lt : η < 1 := lt_of_le_of_lt hη eta_odd_lt_one
  exact hlow_positivity_of_active v d a s η hLow h_eta_lt hs

/-!
### 4. Unified Sector Parity Operator Enclosure
-/

/-- The certified error bound for either parity sector satisfies `(cert p).eta_bound < 1`. -/
theorem sector_eta_lt_one (p : SectorParity) :
    (certificate_of_parity p).eta_bound < 1 := by
  cases p with
  | even => exact eta_even_lt_one
  | odd => exact eta_odd_lt_one

/-- Unified sector Schur operator bound across parity sectors:
`(1 - (cert p).eta_bound) * s ≤ a + ∑ i, (2 * v i * y i + d i * (y i)^2)`. -/
theorem sector_hlow_schur_bound
    (p : SectorParity)
    {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ (certificate_of_parity p).eta_bound) (hs : 0 ≤ s) :
    (1 - (certificate_of_parity p).eta_bound) * s ≤
      a + ∑ i, (2 * v i * y i + d i * (y i)^2) := by
  cases p with
  | even => exact even_hlow_schur_bound d v y hd a s η hLow hη hs
  | odd => exact odd_hlow_schur_bound d v y hd a s η hLow hη hs

/-- Strict positivity of the sector Schur complement for either parity sector when `s > 0`. -/
theorem sector_hlow_strictly_positive
    (p : SectorParity)
    {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (d : ι → ℝ) (a s η : ℝ)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hη : η ≤ (certificate_of_parity p).eta_bound) (hs : 0 < s) :
    0 < a - ∑ i, (v i)^2 / d i := by
  cases p with
  | even => exact even_hlow_strictly_positive v d a s η hLow hη hs
  | odd => exact odd_hlow_strictly_positive v d a s η hLow hη hs

/-!
### 5. Full Operator Certificate Embedding Theorems
-/

/-- Full operator certificate embedding for the even sector:
Given the low-frequency Schur complement bound and the Hilbert tail bound certified by `CertificateData`,
the even sector quadratic form satisfies `margin_even_bound * s ≤ Q`. -/
theorem even_operator_certificate_embedding
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_nonneg : 0 ≤ s)
    (hη : η ≤ eta_even_bound)
    (hτ : τ ≤ tau_even_bound) :
    margin_even_bound * s ≤ Q := by
  have h := lean_certificate_lower_bound SectorParity.even d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ
  exact h

/-- Strict positivity of the full quadratic form in the even sector from the certificate embedding. -/
theorem even_operator_certificate_positivity
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
    0 < Q := by
  exact lean_certificate_positivity SectorParity.even d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

/-- Full operator certificate embedding for the odd sector:
Given the low-frequency Schur complement bound and the Hilbert tail bound certified by `CertificateData`,
the odd sector quadratic form satisfies `margin_odd_bound * s ≤ Q`. -/
theorem odd_operator_certificate_embedding
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_nonneg : 0 ≤ s)
    (hη : η ≤ eta_odd_bound)
    (hτ : τ ≤ tau_odd_bound) :
    margin_odd_bound * s ≤ Q := by
  have h := lean_certificate_lower_bound SectorParity.odd d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ
  exact h

/-- Strict positivity of the full quadratic form in the odd sector from the certificate embedding. -/
theorem odd_operator_certificate_positivity
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
    0 < Q := by
  exact lean_certificate_positivity SectorParity.odd d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

/-- Unified operator certificate embedding across parity sectors:
`(cert p).margin_bound * s ≤ Q`. -/
theorem unified_operator_certificate_embedding
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
    (certificate_of_parity p).margin_bound * s ≤ Q :=
  lean_certificate_lower_bound p d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ

/-- Unified operator certificate strict positivity across parity sectors when `s > 0`. -/
theorem unified_operator_certificate_positivity
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
    0 < Q :=
  lean_certificate_positivity p d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

end RHLowCertificate

