import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/- The analytic finite/remaining-tail certificate. All lower bounds are explicit
hypotheses; this file does not import Arb output as an axiom. -/
namespace RHWeightedSchur
open scoped BigOperators

lemma scalar_completion {d v y : ℝ} (hd : 0 < d) :
    -(v^2 / d) ≤ 2*v*y + d*y^2 := by
  have he : d * (v^2 / d) = v^2 := mul_div_cancel₀ _ (ne_of_gt hd)
  have hs := sq_nonneg (d*y+v)
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith

lemma hilbert_completion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℝ} (hd : 0 < d) (v y : E) :
    -(‖v‖^2 / d) ≤ 2 * inner ℝ v y + d*‖y‖^2 := by
  have hc : -(‖v‖ * ‖y‖) ≤ inner ℝ v y :=
    (abs_le.mp (abs_real_inner_le_norm v y)).1
  have hm := mul_nonneg hd.le (sub_nonneg.mpr hc)
  have he : d * (‖v‖^2 / d) = ‖v‖^2 := mul_div_cancel₀ _ (ne_of_gt hd)
  have hs := sq_nonneg (d*‖y‖-‖v‖)
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith

/-- Low block, explicitly completed finite middle band, and arbitrary Hilbert tail.
The tail is not truncated. s will be the squared preconditioned low coefficient norm. -/
theorem certificate_lower_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d v y : ι → ℝ) (hd : ∀ i, 0 < d i)
    (r z : E) {dM a Q s η τ : ℝ} (hdM : 0 < dM)
    (hQ : a + (∑ i, (2 * v i * y i + d i * (y i)^2)) +
      2 * inner ℝ r z + dM * ‖z‖^2 ≤ Q)
    (hLow : (1-η)*s ≤ a - ∑ i, (v i)^2 / d i)
    (hResidual : ‖r‖^2 / dM ≤ τ*s) :
    (1-η-τ)*s ≤ Q := by
  have hfin := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => scalar_completion (hd i) (v := v i) (y := y i))
  rw [Finset.sum_neg_distrib] at hfin
  have htail := hilbert_completion hdM r z
  nlinarith

/-- A fixed approximant c in the projected space safely bounds the orthogonal residual. -/
lemma orthogonal_residual_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u p c : E) (horth : inner ℝ (u-p) (p-c) = 0) :
    ‖u-p‖^2 ≤ ‖u-c‖^2 := by
  have h := norm_add_sq_real (u-p) (p-c)
  rw [sub_add_sub_cancel, horth] at h
  nlinarith [sq_nonneg ‖p-c‖]

/-- Strictness requires positive low norm; the zero-low-vector case remains a separate obligation. -/
lemma positive_of_margin {s η τ Q : ℝ} (hs : 0 < s) (hmargin : η+τ < 1)
    (hbound : (1-η-τ)*s ≤ Q) : 0 < Q := by
  have hm : 0 < 1-η-τ := by linarith
  exact lt_of_lt_of_le (mul_pos hm hs) hbound

end RHWeightedSchur

