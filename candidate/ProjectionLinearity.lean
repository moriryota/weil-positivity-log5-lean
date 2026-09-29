import RawProjection
namespace RHRawProjection

theorem seed_add (L a r : ℝ) (u v : ℝ → ℝ) :
    seed L a r (u+v) = seed L a r u + seed L a r v := by
  funext t
  by_cases ht : t ∈ Set.Ico (-L) (L-2*a)
  · simp only [seed, Set.indicator_of_mem ht, Pi.add_apply, RHChainCoordinates.coefficient]
    ring
  · simp [seed, Set.indicator_of_notMem ht]

theorem seed_smul (L a r c : ℝ) (u : ℝ → ℝ) :
    seed L a r (c • u) = c • seed L a r u := by
  funext t
  by_cases ht : t ∈ Set.Ico (-L) (L-2*a)
  · simp only [seed, Set.indicator_of_mem ht, Pi.smul_apply, smul_eq_mul,
      RHChainCoordinates.coefficient]
    ring
  · simp [seed, Set.indicator_of_notMem ht]

theorem project_add (L a r : ℝ) (u v : ℝ → ℝ) :
    project L a r (u+v) = project L a r u + project L a r v := by
  funext t
  simp only [project, seed_add, Pi.add_apply]
  ring

theorem project_smul (L a r c : ℝ) (u : ℝ → ℝ) :
    project L a r (c • u) = c • project L a r u := by
  funext t
  simp only [project, seed_smul, Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def projectLinear (L a r : ℝ) : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := project L a r
  map_add' := project_add L a r
  map_smul' := project_smul L a r
theorem project_support (u : ℝ → ℝ) {L a r x : ℝ} (ha : 0≤a)
    (hx : x ∉ Set.Icc (-L) L) : project L a r u x = 0 := by
  have h1 : x ∉ Set.Ico (-L) (L-2*a) := by
    intro h; apply hx; rcases h with ⟨hl,hu⟩; constructor <;> linarith
  have h2 : x-a ∉ Set.Ico (-L) (L-2*a) := by
    intro h; apply hx; rcases h with ⟨hl,hu⟩; constructor <;> linarith
  have h3 : x-2*a ∉ Set.Ico (-L) (L-2*a) := by
    intro h; apply hx; rcases h with ⟨hl,hu⟩; constructor <;> linarith
  simp [project, seed, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
    Set.indicator_of_notMem h3]
end RHRawProjection
