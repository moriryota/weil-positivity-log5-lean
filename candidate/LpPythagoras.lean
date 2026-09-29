import RawPythagoras
import ProjectionNormIntegral
import LpLinearity
import ChainGeometry
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace RHRawProjection

theorem lp_pythagoras {L a r : ℝ} (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    ‖f‖^2 = ‖projectLp L a r f‖^2+‖f-projectLp L a r f‖^2 := by
  have h := integral_pythagoras (r := r) ((Icc (-L) L).indicator (f : ℝ → ℝ))
    (RHZeroExtension.lp_zero_extension_memLp L f) ha h2 h3
  have hz := RHProjectionNorm.integral_sq_norm_of_ae L f
    ((Icc (-L) L).indicator (f : ℝ → ℝ)) (indicator_ae_eq_restrict measurableSet_Icc)
  rw [hz, RHProjectionNorm.integral_project_sq_norm,
    RHProjectionNorm.integral_residual_sq_norm] at h
  exact h

theorem lp_contraction {L a r : ℝ} (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ‖projectLp L a r f‖ ≤ ‖f‖ := by
  have h := lp_pythagoras (r := r) ha h2 h3 f
  nlinarith [sq_nonneg ‖f-projectLp L a r f‖, norm_nonneg f, norm_nonneg (projectLp L a r f)]

theorem lp_residual_orthogonal {L a r : ℝ} (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    inner ℝ (projectLp L a r f) (f-projectLp L a r f) = 0 := by
  have h := lp_pythagoras (r := r) ha h2 h3 f
  have he := norm_add_sq_real (projectLp L a r f) (f-projectLp L a r f)
  have hs : projectLp L a r f + (f-projectLp L a r f) = f := by abel
  rw [hs] at he
  linarith

noncomputable def projectLpContinuous {L a r : ℝ} (ha : 0<a)
    (h2 : 2*a≤2*L) (h3 : 2*L≤3*a) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (-L) L)) :=
  (projectLpLinear L a r).mkContinuous 1 (by
    intro f
    simpa [projectLpLinear] using lp_contraction (r := r) ha h2 h3 f)

theorem log5_lp_pythagoras (r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    ‖f‖^2 = ‖projectLp (Real.log 5/2) (Real.log 2) r f‖^2 +
      ‖f-projectLp (Real.log 5/2) (Real.log 2) r f‖^2 := by
  have h := RHChainGeometry.log5_geometry
  exact lp_pythagoras h.1 (by linarith [h.2.1]) (by linarith [h.2.2.1]) f
end RHRawProjection
