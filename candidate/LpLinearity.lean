import ProjectionLp
import ProjectionLinearity
open MeasureTheory Set
namespace RHRawProjection

theorem projectLp_add (L a r : ℝ)
    (f g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    projectLp L a r (f+g) = projectLp L a r f + projectLp L a r g := by
  have hfg : (Icc (-L) L).indicator ((f+g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ → ℝ) =ᵐ[volume]
      (Icc (-L) L).indicator ((f : ℝ → ℝ)+(g : ℝ → ℝ)) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp (Lp.coeFn_add f g)
  have hc := project_congr_ae L a r hfg
  have hi : (Icc (-L) L).indicator ((f : ℝ → ℝ)+(g : ℝ → ℝ)) =
      (Icc (-L) L).indicator (f : ℝ → ℝ)+(Icc (-L) L).indicator (g : ℝ → ℝ) := by
    funext x
    by_cases hx : x ∈ Icc (-L) L <;> simp [hx]
  rw [hi, project_add] at hc
  have hcr : project L a r ((Icc (-L) L).indicator ((f+g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ → ℝ)) =ᵐ[volume.restrict (Icc (-L) L)]
      project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) +
        project L a r ((Icc (-L) L).indicator (g : ℝ → ℝ)) := ae_restrict_of_ae hc
  apply Lp.ext
  filter_upwards [coeFn_projectLp L a r (f+g), coeFn_projectLp L a r f,
    coeFn_projectLp L a r g, Lp.coeFn_add (projectLp L a r f) (projectLp L a r g), hcr] with x hs hf hg hadd h
  simpa only [Pi.add_apply, hs, hadd, hf, hg] using h

theorem projectLp_smul (L a r c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    projectLp L a r (c • f) = c • projectLp L a r f := by
  have hfg : (Icc (-L) L).indicator ((c • f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ → ℝ) =ᵐ[volume]
      (Icc (-L) L).indicator (c • (f : ℝ → ℝ)) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp (Lp.coeFn_smul c f)
  have hc := project_congr_ae L a r hfg
  have hi : (Icc (-L) L).indicator (c • (f : ℝ → ℝ)) =
      c • (Icc (-L) L).indicator (f : ℝ → ℝ) := by
    funext x
    by_cases hx : x ∈ Icc (-L) L <;> simp [hx]
  rw [hi, project_smul] at hc
  have hcr : project L a r ((Icc (-L) L).indicator ((c • f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ → ℝ)) =ᵐ[volume.restrict (Icc (-L) L)]
      c • project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ)) := ae_restrict_of_ae hc
  apply Lp.ext
  filter_upwards [coeFn_projectLp L a r (c • f), coeFn_projectLp L a r f,
    Lp.coeFn_smul c (projectLp L a r f), hcr] with x hs hf hsmul h
  simpa only [Pi.smul_apply, smul_eq_mul, hs, hsmul, hf] using h

noncomputable def projectLpLinear (L a r : ℝ) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Icc (-L) L)) where
  toFun := projectLp L a r
  map_add' := projectLp_add L a r
  map_smul' := projectLp_smul L a r
end RHRawProjection
