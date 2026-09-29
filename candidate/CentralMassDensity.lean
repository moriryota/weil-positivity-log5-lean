import ProjectionCoordinates
import ChainGeometry
import Mathlib.Tactic

open Set

namespace RHCentralDensity

/-- Difference between central projected mass and its fixed fraction of total projected mass. -/
noncomputable def density (L a b r : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((Ioo (L-b) (-L+b)).indicator (RHRawProjection.project L a r u) x)^2 -
    (r^2/(2+r^2)) * (RHRawProjection.project L a r u x)^2

theorem triple_zero {L a b r : ℝ} (u : ℝ → ℝ)
    (ha : 0 < a) (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a)
    (hW : 2*L < a+b) (hab : b < 2*a)
    {t : ℝ} (ht : t ∈ Ico (-L) (L-2*a)) :
    density L a b r u t + density L a b r u (t+a) +
      density L a b r u (t+2*a) = 0 := by
  have hm := RHChainGeometry.middle_in_gap hW ht
  obtain ⟨hl,hr⟩ := RHChainGeometry.outside_gap hab ht
  unfold density
  rw [indicator_of_notMem hl, indicator_of_mem hm, indicator_of_notMem hr,
    RHRawProjection.project_triple_left u ha h2 h3 ht,
    RHRawProjection.project_triple_middle u ha h2 h3 ht,
    RHRawProjection.project_triple_right u ha h2 h3 ht]
  have hd : 2+r^2 ≠ 0 := by positivity
  field_simp
  ring

theorem double_zero {L a b r : ℝ} (u : ℝ → ℝ)
    (ha : 0 < a) (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a)
    {t : ℝ} (ht : t ∈ Ico (L-2*a) (-L+a)) :
    density L a b r u t + density L a b r u (t+a) = 0 := by
  obtain ⟨hl,hr⟩ := RHRawProjection.project_double_zero (r := r) u ha h2 h3 ht
  simp [density, Set.indicator, hl, hr]

end RHCentralDensity

