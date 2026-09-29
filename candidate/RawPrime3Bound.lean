import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ProjectionNormIntegral
import CentralMultiplierLp
import ShiftChain
import ShiftOverlap
import ActualCorrelation

open MeasureTheory Set
open RHCentralMultiplier RHProjectionNorm RHActualCorrelation RHShiftChain

namespace RHRawPrime3

/-- The integral of f^2 on the central subinterval Ico (L-b) (-L+b) equals the squared norm of centralLp L b f. -/
theorem central_sq_integral (L b : ℝ) (hW : b ≤ 2*L)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (∫ x in Ico (L-b) (-L+b), (f x)^2) = ‖centralLp L b f‖^2 := by
  have hsub : Ioo (L-b) (-L+b) ⊆ Ico (-L) L := by
    intro x hx
    rcases hx with ⟨h1, h2⟩
    constructor <;> linarith
  have h_inter : Ico (-L) L ∩ Ioo (L-b) (-L+b) = Ioo (L-b) (-L+b) := inter_eq_right.mpr hsub
  have hg : (fun x => ((Ioo (L-b) (-L+b)).indicator (f : ℝ → ℝ) x)^2) =
      (Ioo (L-b) (-L+b)).indicator (fun x => (f x)^2) := by
    ext x
    by_cases hx : x ∈ Ioo (L-b) (-L+b)
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  have h1 : (∫ x in Ico (-L) L, ((Ioo (L-b) (-L+b)).indicator (f : ℝ → ℝ) x)^2) = ‖centralLp L b f‖^2 :=
    integral_sq_norm_of_ae L (centralLp L b f) _ (coeFn_centralLp L b f).symm
  rw [hg, setIntegral_indicator measurableSet_Ioo, h_inter, ← integral_Ico_eq_integral_Ioo] at h1
  exact h1

/-- Two-point chain bound for shift b: 2 * autocorr L f b ≤ ‖f‖^2 - ‖centralLp L b f‖^2. -/
theorem prime3_two_point_bound (L b : ℝ) (hb : 0 ≤ b) (hW : b ≤ 2*L) (h2b : 2*L ≤ 2*b)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    2 * autocorr L f b ≤ ‖f‖^2 - ‖centralLp L b f‖^2 := by
  have h_central : (∫ x in Ico (L-b) (-L+b), (f x)^2) = ‖centralLp L b f‖^2 :=
    central_sq_integral L b hW f

  have hf_sq : IntegrableOn (fun x => (f x)^2) (Ico (-L) L) := sq_integrableOn L f
  have h1_int : IntegrableOn (fun x => (f x)^2) (Ico (-L) (-L+b)) :=
    hf_sq.mono_set (Ico_subset_Ico le_rfl (by linarith))
  have h_decomp : (∫ x in Ico (-L) L, (f x)^2) =
      (∫ x in Ico (-L) (L-b), (f x)^2) + (∫ x in Ico (L-b) (-L+b), (f x)^2) + (∫ x in Ico (-L+b) L, (f x)^2) := by
    have hs1 := ico_split (fun x => (f x)^2) (s := -L) (m := -L+b) (e := L) (by linarith) (by linarith) hf_sq
    have hs2 := ico_split (fun x => (f x)^2) (s := -L) (m := L-b) (e := -L+b) (by linarith) (by linarith) h1_int
    linarith

  rw [integral_sq_norm L f, h_central] at h_decomp
  have h_norm_diff : ‖f‖^2 - ‖centralLp L b f‖^2 =
      (∫ x in Ico (-L) (L-b), (f x)^2) + (∫ x in Ico (-L+b) L, (f x)^2) := by
    linarith

  have h_shift_int : (∫ x in Ico (-L) (L-b), (f (x+b))^2) = (∫ x in Ico (-L+b) L, (f x)^2) := by
    have hs := ico_shift (fun x => (f x)^2) (-L) (L-b) b
    have h2 : L-b+b = L := by ring
    rw [h2] at hs
    exact hs

  have hi_cross : IntegrableOn (fun x => f x * f (x+b)) (Ico (-L) (L-b)) := overlap_integrable L f b hb
  have hi_sq1 : IntegrableOn (fun x => (f x)^2) (Ico (-L) (L-b)) :=
    hf_sq.mono_set (Ico_subset_Ico le_rfl (by linarith))
  have hi_sq2 : IntegrableOn (fun x => (f (x+b))^2) (Ico (-L) (L-b)) := by
    apply (ico_shift_integrable (fun x => (f x)^2) (-L) (L-b) b).mpr
    rw [show L-b+b = L by ring]
    exact hf_sq.mono_set (Ico_subset_Ico (by linarith) le_rfl)

  have h_diff_int : 0 ≤ ∫ x in Ico (-L) (L-b), ((f x)^2 + (f (x+b))^2 - 2 * (f x * f (x+b))) := by
    apply setIntegral_nonneg measurableSet_Ico
    intro x _
    have h_sq : 0 ≤ (f x - f (x+b))^2 := sq_nonneg _
    nlinarith

  have h_sum_int : IntegrableOn (fun x => (f x)^2 + (f (x+b))^2) (Ico (-L) (L-b)) := hi_sq1.add hi_sq2
  have h_two_cross : IntegrableOn (fun x => 2 * (f x * f (x+b))) (Ico (-L) (L-b)) := hi_cross.const_mul 2
  rw [integral_sub h_sum_int h_two_cross, integral_add hi_sq1 hi_sq2, integral_const_mul] at h_diff_int

  have h_ac : autocorr L f b = ∫ x in Ico (-L) (L-b), f x * f (x+b) := by
    unfold autocorr
    exact RHShiftOverlap.overlap_integral (f : ℝ → ℝ) (-L) L b hb

  rw [← h_ac, h_shift_int] at h_diff_int
  linarith

end RHRawPrime3
