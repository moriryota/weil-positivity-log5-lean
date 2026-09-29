import ShiftOverlap
import ZeroExtensionCorrelation
import ShiftChain
import ThreePointSOS
import ChainGeometry
open MeasureTheory Set
namespace RHActualCorrelation
noncomputable def autocorr (L : ℝ) (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (d : ℝ) : ℝ :=
  ∫ t, (Icc (-L) L).indicator (f : ℝ → ℝ) t * (Icc (-L) L).indicator (f : ℝ → ℝ) (t+d)

theorem overlap_integrable (L : ℝ) (f : Lp ℝ 2 (volume.restrict (Icc (-L) L)))
    (d : ℝ) (hd : 0≤d) :
    IntegrableOn (fun t => f t*f (t+d)) (Ico (-L) (L-d)) := by
  have hi := RHZeroExtension.lp_zero_extension_correlation_integrable L f d
  rw [RHShiftOverlap.product_eq_indicator (f : ℝ → ℝ) (-L) L d hd] at hi
  exact ((integrable_indicator_iff measurableSet_Icc).mp hi).mono_set Ico_subset_Icc_self

theorem negative_shift (L : ℝ) (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (d : ℝ) :
    (∫ t, (Icc (-L) L).indicator (f : ℝ → ℝ) t *
      (Icc (-L) L).indicator (f : ℝ → ℝ) (t-d)) = autocorr L f d := by
  have h := (measurePreserving_add_right volume d).integral_comp
    (Homeomorph.addRight d).measurableEmbedding
    (fun t => (Icc (-L) L).indicator (f : ℝ → ℝ) t *
      (Icc (-L) L).indicator (f : ℝ → ℝ) (t-d))
  simpa only [add_sub_cancel_right, mul_comm, autocorr] using h.symm

theorem weighted_chain {L a : ℝ} (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (alpha beta : ℝ) :
    2*alpha*autocorr L f a + 2*beta*autocorr L f (2*a) =
      (∫ t in Ico (-L) (L-2*a), RHThreePoint.form alpha beta (f t) (f (t+a)) (f (t+2*a))) +
      (∫ t in Ico (L-2*a) (-L+a), 2*alpha*(f t*f (t+a))) := by
  have hi1 := overlap_integrable L f a ha.le
  have hi2 := overlap_integrable L f (2*a) (by positivity)
  have hl : -L+2*L=L := by ring
  have hh := RHShiftChain.weighted_product_chain (f : ℝ → ℝ) alpha beta
    (s := -L) (W := 2*L) ha h2 h3
    (by simpa only [hl] using hi1) (by simpa only [hl] using hi2)
  rw [hl] at hh
  unfold autocorr
  rw [RHShiftOverlap.overlap_integral _ _ _ a ha.le,
    RHShiftOverlap.overlap_integral _ _ _ (2*a) (by positivity), hh]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  unfold RHThreePoint.form
  ring

theorem log5_weighted_chain
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))))
    (alpha beta : ℝ) :
    2*alpha*autocorr (Real.log 5/2) f (Real.log 2) +
      2*beta*autocorr (Real.log 5/2) f (2*Real.log 2) =
      (∫ t in Ico (-(Real.log 5/2)) (Real.log 5/2-2*Real.log 2),
        RHThreePoint.form alpha beta (f t) (f (t+Real.log 2)) (f (t+2*Real.log 2))) +
      (∫ t in Ico (Real.log 5/2-2*Real.log 2) (-(Real.log 5/2)+Real.log 2),
        2*alpha*(f t*f (t+Real.log 2))) := by
  have h := RHChainGeometry.log5_geometry
  exact weighted_chain h.1 (by linarith [h.2.1]) (by linarith [h.2.2.1]) f alpha beta
end RHActualCorrelation
