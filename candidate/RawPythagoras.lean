import ProjectionCoordinates
import ProjectionLp
import RealChainDecomposition
open MeasureTheory Set
namespace RHRawProjection

lemma square_integrable {u : ℝ → ℝ} (hu : MemLp u 2 volume) :
    Integrable (fun x => (u x)^2) volume := by
  have he : (fun x => (u x)^2) = u*u := by
    funext x
    simp only [pow_two, Pi.mul_apply]
  rw [he]
  exact hu.integrable_mul hu

theorem integral_pythagoras {L a r : ℝ} (u : ℝ → ℝ) (hu : MemLp u 2 volume)
    (ha : 0 < a) (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) :
    (∫ x in Ico (-L) L, (u x)^2) =
      (∫ x in Ico (-L) L, (project L a r u x)^2) +
      (∫ x in Ico (-L) L, (u x-project L a r u x)^2) := by
  have hp := project_memLp L a r hu
  have hres : MemLp (fun x => u x-project L a r u x) 2 volume := hu.sub hp
  have hiu := square_integrable hu
  have hip := square_integrable hp
  have hir := square_integrable hres
  let g : ℝ → ℝ := fun x => (u x)^2 - (project L a r u x)^2 - (u x-project L a r u x)^2
  have hig : Integrable g volume := (hiu.sub hip).sub hir
  have htriple (t : ℝ) (ht : t ∈ Ico (-L) (L-2*a)) :
      g t + g (t+a) + g (t+2*a) = 0 := by
    dsimp only [g]
    rw [project_triple_left u ha h2 h3 ht, project_triple_middle u ha h2 h3 ht,
      project_triple_right u ha h2 h3 ht]
    have h := RHChainCoordinates.norm_split r (u t) (u (t+a)) (u (t+2*a))
    nlinarith
  have hdouble (t : ℝ) (ht : t ∈ Ico (L-2*a) (-L+a)) : g t + g (t+a) = 0 := by
    obtain ⟨hl,hr⟩ := project_double_zero (r := r) u ha h2 h3 ht
    simp only [g, hl, hr, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, sub_self, add_zero]
  have hc := RHRealChain.integral_chain_decomposition g (-L) (2*L) a ha h2 h3 hig.integrableOn
  simp only [show -L+2*L = L by ring] at hc
  have htint : (∫ t in Ico (-L) (L-2*a), g t+g (t+a)+g (t+2*a)) = 0 := by
    calc
      _ = ∫ _t in Ico (-L) (L-2*a), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ico htriple
      _ = 0 := by simp
  have hbint : (∫ t in Ico (L-2*a) (-L+a), g t+g (t+a)) = 0 := by
    calc
      _ = ∫ _t in Ico (L-2*a) (-L+a), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ico hdouble
      _ = 0 := by simp
  rw [htint, hbint, add_zero] at hc
  dsimp only [g] at hc
  have hisub : Integrable (fun x => (u x)^2 - (project L a r u x)^2) volume := hiu.sub hip
  rw [integral_sub hisub.integrableOn hir.integrableOn,
    integral_sub hiu.integrableOn hip.integrableOn] at hc
  linarith

end RHRawProjection
