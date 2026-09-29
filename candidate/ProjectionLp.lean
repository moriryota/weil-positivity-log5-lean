import RawProjection
import ZeroExtensionCorrelation
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

open MeasureTheory Set

namespace RHRawProjection

theorem coefficient_memLp (a r : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 volume) :
    MemLp (fun t => RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a))) 2 volume := by
  have h := ((hu.add ((RHZeroExtension.translate_memLp hu a).const_mul r)).add
    (RHZeroExtension.translate_memLp hu (2*a))).mul_const (2+r^2)⁻¹
  simpa only [RHChainCoordinates.coefficient, div_eq_mul_inv, Pi.add_apply] using h

theorem seed_memLp (L a r : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 volume) :
    MemLp (seed L a r u) 2 volume :=
  MemLp.indicator measurableSet_Ico (coefficient_memLp a r hu)

theorem project_memLp (L a r : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 volume) :
    MemLp (project L a r u) 2 volume := by
  have hs := seed_memLp L a r hu
  have h := (hs.add ((RHZeroExtension.translate_memLp hs (-a)).const_mul r)).add
    (RHZeroExtension.translate_memLp hs (-(2*a)))
  convert h using 1 <;> ext x <;> simp [project, sub_eq_add_neg]

theorem project_zero_extension_memLp (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    MemLp (project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ))) 2 volume :=
  project_memLp L a r (RHZeroExtension.lp_zero_extension_memLp L f)

theorem project_restrict_memLp (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    MemLp (project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ))) 2
      (volume.restrict (Icc (-L) L)) :=
  (project_zero_extension_memLp L a r f).restrict _

/-- The raw chain projection of the zero extension, restricted back to the original interval. -/
noncomputable def projectLp (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) :=
  (project_restrict_memLp L a r f).toLp _

theorem coeFn_projectLp (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (projectLp L a r f : ℝ → ℝ) =ᵐ[volume.restrict (Icc (-L) L)]
      project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) :=
  (project_restrict_memLp L a r f).coeFn_toLp

theorem translate_congr_ae {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) (d : ℝ) :
    (fun x => u (x+d)) =ᵐ[volume] (fun x => v (x+d)) :=
  (measurePreserving_add_right volume d).quasiMeasurePreserving.ae_eq h

theorem seed_congr_ae (L a r : ℝ) {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) :
    seed L a r u =ᵐ[volume] seed L a r v := by
  filter_upwards [h, translate_congr_ae h a, translate_congr_ae h (2*a)] with x hx hx₁ hx₂
  by_cases ht : x ∈ Ico (-L) (L-2*a)
  · simp [seed, ht, hx, hx₁, hx₂]
  · simp [seed, ht]

theorem project_congr_ae (L a r : ℝ) {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) :
    project L a r u =ᵐ[volume] project L a r v := by
  have hs := seed_congr_ae L a r h
  filter_upwards [hs, translate_congr_ae hs (-a), translate_congr_ae hs (-(2*a))] with x hx hx₁ hx₂
  simp only [project, sub_eq_add_neg, hx, hx₁, hx₂]

end RHRawProjection


