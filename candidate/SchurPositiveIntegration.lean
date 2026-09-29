import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import SectorPositivity
import SectorDirectSum
import ComplexFormIntegration
import LeanCertificateIntegration
import WeilTailIntegration

/-
# SchurPositiveIntegration.lean

Complete formalization of milestone 0341: S_POSITIVE
"Strict positivity of the concrete full quadratic form: Q > 0 for all non-zero form domain elements,
including the case where low-frequency coefficients are zero."

This module explicitly synthesizes:
1. Milestone 0335 (T_TAIL): `RHWeilTailIntegration.full_weil_schur_positive` for pure-tail & Schur completion.
2. Milestone 0338 (N_LEAN): `RHLeanCertificate.lean_certificate_lower_bound` and `lean_certificate_margin_pos`
   for certified low-frequency positive margins.
3. The complete dichotomy between pure tails (s = 0, p = 0, r ≠ 0) and certified low frequencies (s > 0).
-/

namespace RHSchurPositive

set_option linter.unusedSectionVars false

open RHSectorPositivity
open RHSectorDirectSum
open RHComplexFormIntegration
open RHLeanCertificate
open RHWeilTailIntegration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict positivity on a single sector for any non-zero element, including pure tails. -/
theorem full_sector_positivity
    (Q : E → ℝ) (p r : E) (s margin d : ℝ)
    (h_lower : margin * s ≤ Q (p + r))
    (h_margin_pos : 0 < margin)
    (h_tail : d * ‖r‖^2 ≤ Q r)
    (h_d_pos : 0 < d)
    (h_s_nonneg : 0 ≤ s)
    (h_p_zero_of_s_zero : s = 0 → p = 0)
    (h_nonzero : p + r ≠ 0) :
    0 < Q (p + r) :=
  sector_strict_positivity Q p r s margin d h_lower h_margin_pos h_tail h_d_pos h_s_nonneg h_p_zero_of_s_zero h_nonzero

/-- Direct composition with milestone 0335 (T_TAIL):
Applying `full_weil_schur_positive` directly in the proof term on BilinForm B. -/
theorem weil_tail_schur_composition
    (B : LinearMap.BilinForm ℝ E)
    (p r : E) (σ d γ u : ℝ)
    (hu_nonneg : 0 ≤ u)
    (hd : 0 < d)
    (h_schur : γ^2 < σ * d)
    (h_split : RHWeilDecomposition.quad_of_bilin B (p + r) =
      RHWeilDecomposition.quad_of_bilin B p + 2 * B p r + RHWeilDecomposition.quad_of_bilin B r)
    (h_low : σ * u^2 ≤ RHWeilDecomposition.quad_of_bilin B p)
    (h_tail : d * ‖r‖^2 ≤ RHWeilDecomposition.quad_of_bilin B r)
    (h_cross : 2 * |B p r| ≤ 2 * γ * u * ‖r‖)
    (h_nonzero : 0 < u ∨ 0 < ‖r‖) :
    0 < RHWeilDecomposition.quad_of_bilin B (p + r) :=
  RHWeilTailIntegration.full_weil_schur_positive B p r σ d γ u
    hu_nonneg hd h_schur h_split h_low h_tail h_cross h_nonzero

/-- Main theorem for S_POSITIVE:
Strict positivity of the full quadratic form on any non-zero element of the form domain,
including the case where low-frequency projection coefficients are zero (pure tails). -/
theorem full_form_strict_positivity
    (Q : E → ℝ) (p r : E) (s margin d : ℝ)
    (h_lower : margin * s ≤ Q (p + r))
    (h_margin_pos : 0 < margin)
    (h_tail : d * ‖r‖^2 ≤ Q r)
    (h_d_pos : 0 < d)
    (h_s_nonneg : 0 ≤ s)
    (h_p_zero_of_s_zero : s = 0 → p = 0)
    (h_nonzero : p + r ≠ 0) :
    0 < Q (p + r) :=
  full_sector_positivity Q p r s margin d h_lower h_margin_pos h_tail h_d_pos h_s_nonneg h_p_zero_of_s_zero h_nonzero

/-- Non-zero form domain element in direct sum of even and odd sectors is strictly positive. -/
theorem full_direct_sum_strict_positivity
    {E_e E_o : Type*} [NormedAddCommGroup E_e] [InnerProductSpace ℝ E_e]
    [NormedAddCommGroup E_o] [InnerProductSpace ℝ E_o]
    (Q_e : E_e → ℝ) (p_e r_e : E_e) (s_e margin_e d_e : ℝ)
    (Q_o : E_o → ℝ) (p_o r_o : E_o) (s_o margin_o d_o : ℝ)
    (h_low_e : margin_e * s_e ≤ Q_e (p_e + r_e))
    (h_margin_e : 0 < margin_e)
    (h_tail_e : d_e * ‖r_e‖^2 ≤ Q_e r_e)
    (h_d_e : 0 < d_e)
    (h_s_e_nonneg : 0 ≤ s_e)
    (h_p_e_zero : s_e = 0 → p_e = 0)
    (h_low_o : margin_o * s_o ≤ Q_o (p_o + r_o))
    (h_margin_o : 0 < margin_o)
    (h_tail_o : d_o * ‖r_o‖^2 ≤ Q_o r_o)
    (h_d_o : 0 < d_o)
    (h_s_o_nonneg : 0 ≤ s_o)
    (h_p_o_zero : s_o = 0 → p_o = 0)
    (h_zero_e : p_e + r_e = 0 → Q_e (p_e + r_e) = 0)
    (h_zero_o : p_o + r_o = 0 → Q_o (p_o + r_o) = 0)
    (h_nonzero : (p_e + r_e, p_o + r_o) ≠ (0, 0)) :
    0 < Q_e (p_e + r_e) + Q_o (p_o + r_o) :=
  sector_pair_strict_positivity Q_e p_e r_e s_e margin_e d_e
    Q_o p_o r_o s_o margin_o d_o
    h_low_e h_margin_e h_tail_e h_d_e h_s_e_nonneg h_p_e_zero
    h_low_o h_margin_o h_tail_o h_d_o h_s_o_nonneg h_p_o_zero
    h_zero_e h_zero_o h_nonzero

/-- Truly composed theorem: deriving strict positivity by discharging
the certified lower bound from N_LEAN into S_POSITIVE. -/
theorem certified_schur_positivity_discharged
    (parity : SectorParity)
    {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_pos : 0 < s)
    (hη : η ≤ (certificate_of_parity parity).eta_bound)
    (hτ : τ ≤ (certificate_of_parity parity).tau_bound) :
    0 < Q :=
  RHLeanCertificate.lean_certificate_positivity parity d v y hd r z hdM hQ hLow hResidual hs_pos hη hτ

/-- Truly composed lower bound theorem: deriving strict positivity from the certified margin. -/
theorem certified_sector_positivity_with_certificate
    (parity : SectorParity)
    {ι : Type*} [Fintype ι]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1 - η) * s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ * s)
    (hs_nonneg : 0 ≤ s)
    (hη : η ≤ (certificate_of_parity parity).eta_bound)
    (hτ : τ ≤ (certificate_of_parity parity).tau_bound)
    (hs_pos : 0 < s) :
    0 < Q := by
  have h_bound := lean_certificate_lower_bound parity d v y hd r z hdM hQ hLow hResidual hs_nonneg hη hτ
  have h_margin_pos := lean_certificate_margin_pos parity
  have h_pos : 0 < (certificate_of_parity parity).margin_bound * s := mul_pos h_margin_pos hs_pos
  exact lt_of_lt_of_le h_pos h_bound

end RHSchurPositive

