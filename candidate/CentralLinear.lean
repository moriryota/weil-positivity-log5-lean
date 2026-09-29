import CentralMultiplierLp
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
open MeasureTheory Set
namespace RHCentralMultiplier
 theorem centralLp_add (L b : ℝ)
    (f g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    centralLp L b (f+g) = centralLp L b f + centralLp L b g := by
  apply Lp.ext
  filter_upwards [coeFn_centralLp L b (f+g), coeFn_centralLp L b f,
    coeFn_centralLp L b g, Lp.coeFn_add f g,
    Lp.coeFn_add (centralLp L b f) (centralLp L b g)] with x hfg hf hg ha hc
  by_cases hx : x ∈ Ioo (L-b) (-L+b)
  · simpa only [hfg, hc, Pi.add_apply, hf, hg, indicator_of_mem hx] using (show (f+g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) x = f x + g x from ha)
  · simp only [hfg, hc, Pi.add_apply, hf, hg, indicator_of_notMem hx, add_zero]
 theorem centralLp_smul (L b c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    centralLp L b (c • f) = c • centralLp L b f := by
  apply Lp.ext
  filter_upwards [coeFn_centralLp L b (c • f), coeFn_centralLp L b f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (centralLp L b f)] with x hcf hf hs hc
  by_cases hx : x ∈ Ioo (L-b) (-L+b)
  · simpa only [hcf, hc, Pi.smul_apply, hf, indicator_of_mem hx] using (show (c • f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) x = c • f x from hs)
  · simp only [hcf, hc, Pi.smul_apply, hf, indicator_of_notMem hx, smul_zero]
noncomputable def centralLinear (L b : ℝ) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (-L) L)) where
  toFun := centralLp L b
  map_add' := centralLp_add L b
  map_smul' := centralLp_smul L b
noncomputable def centralContinuous (L b : ℝ) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (-L) L)) :=
  (centralLinear L b).mkContinuous 1 (by
    intro f
    simpa [centralLinear] using norm_centralLp_le L b f)
end RHCentralMultiplier
