import ProjectionLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

namespace RHProjectionNorm

theorem sq_integrableOn (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    IntegrableOn (fun x => (f x)^2) (Ico (-L) L) := by
  have h : IntegrableOn (fun x => (f x)^2) (Icc (-L) L) := by
    unfold IntegrableOn
    convert (Lp.memLp f).integrable_mul (Lp.memLp f) using 1
    ext x
    simp [pow_two]
  exact h.mono_set Ico_subset_Icc_self

theorem integral_sq_norm (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (∫ x in Ico (-L) L, (f x)^2) = ‖f‖^2 := by
  rw [← integral_Icc_eq_integral_Ico]
  have h := real_inner_self_eq_norm_sq f
  rw [L2.inner_def] at h
  simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using h

/-- Transfer the norm identity to any representative equal almost everywhere on the interval. -/
theorem integral_sq_norm_of_ae (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (g : ℝ → ℝ)
    (h : g =ᵐ[volume.restrict (Icc (-L) L)] (f : ℝ → ℝ)) :
    (∫ x in Ico (-L) L, (g x)^2) = ‖f‖^2 := by
  rw [← integral_sq_norm L f, ← integral_Icc_eq_integral_Ico,
    ← integral_Icc_eq_integral_Ico]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem integral_project_sq_norm (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (∫ x in Ico (-L) L,
      (RHRawProjection.project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) x)^2) =
      ‖RHRawProjection.projectLp L a r f‖^2 :=
  integral_sq_norm_of_ae L _ _ (RHRawProjection.coeFn_projectLp L a r f).symm

theorem residual_ae (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (fun x => (Icc (-L) L).indicator (f : ℝ → ℝ) x -
      RHRawProjection.project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) x) =ᵐ[volume.restrict (Icc (-L) L)]
      ((f - RHRawProjection.projectLp L a r f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ → ℝ) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    RHRawProjection.coeFn_projectLp L a r f,
    Lp.coeFn_sub f (RHRawProjection.projectLp L a r f)] with x hx hp hs
  simp only [Pi.sub_apply] at hs
  rw [hs, indicator_of_mem hx, hp]

theorem integral_residual_sq_norm (L a r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (∫ x in Ico (-L) L,
      ((Icc (-L) L).indicator (f : ℝ → ℝ) x -
        RHRawProjection.project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) x)^2) =
      ‖f - RHRawProjection.projectLp L a r f‖^2 :=
  integral_sq_norm_of_ae L _ _ (residual_ae L a r f)

end RHProjectionNorm

