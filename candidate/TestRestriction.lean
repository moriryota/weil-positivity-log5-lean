import Final
import ExtensionLp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set
open scoped ENNReal
namespace RHTestRestriction
open RHFormDomain RHBoundedWindow

lemma continuous_bounds {f : ℝ → ℂ} (hf : Continuous f) (L : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ BoundedOn L f M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

lemma c1_lipschitz {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (L : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ LipschitzBoundOn L f M := by
  obtain ⟨M, hM, hb⟩ := continuous_bounds (hf.continuous_deriv_one) L
  refine ⟨M, hM, ?_⟩
  intro x hx y hy
  have hd : ∀ z ∈ Icc (-L) L, HasDerivWithinAt f (deriv f z) (Icc (-L) L) z :=
    fun z _ => ((hf.differentiable (by norm_num)).differentiableAt.hasDerivAt).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-L) L).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

lemma test_memLp {f : ℝ → ℂ} (hf : Continuous f) (L : ℝ) :
    MemLp f 2 (volume.restrict (Icc (-L) L)) := by
  obtain ⟨M, _, hb⟩ := continuous_bounds hf L
  exact bounded_memLp L f hf.measurable M hb

noncomputable def testLp {f : ℝ → ℂ} (hf : Continuous f) (L : ℝ) :
    Lp ℂ 2 (volume.restrict (Icc (-L) L)) := (test_memLp hf L).toLp f

lemma testLp_energy {f : ℝ → ℂ} (hf : Continuous f) (L : ℝ) :
    intervalEnergy L (testLp hf L) = energy (extend L f) :=
  energy_extend_congr_ae (MemLp.coeFn_toLp (test_memLp hf L))

lemma testLp_mem {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L) :
    InDomain L (testLp hf.continuous L) := by
  obtain ⟨M0, h0, hb⟩ := continuous_bounds hf.continuous L
  obtain ⟨M1, h1, hl⟩ := c1_lipschitz hf L
  unfold InDomain
  rw [testLp_energy]
  exact bounded_lipschitz_energy_finite hL f h0 h1 hb hl

lemma extend_eq {f : ℝ → ℂ} {L : ℝ} (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    extend L f = f := by
  funext x
  by_cases hx : x ∈ Icc (-L) L
  · simp [RHFormDomain.extend, hx]
  · have hz : f x = 0 := by
      by_contra hn
      exact hx (abs_le.mp (hs x hn))
    simp [RHFormDomain.extend, hx, hz]

lemma testLp_original_energy {f : ℝ → ℂ} (hf : Continuous f) {L : ℝ}
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    intervalEnergy L (testLp hf L) = energy f := by
  rw [testLp_energy, extend_eq hs]

lemma testLp_ne_zero {f : ℝ → ℂ} (hf : Continuous f) {L : ℝ}
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) (hn : f ≠ 0) :
    testLp hf L ≠ 0 := by
  intro hz
  have ha : (fun x => (testLp hf L) x) =ᵐ[volume.restrict (Icc (-L) L)] f :=
    MemLp.coeFn_toLp (test_memLp hf L)
  rw [hz] at ha
  have he := extend_congr_ae ha
  rw [extend_eq hs] at he
  have he0 : extend L (fun x => (0 : Lp ℂ 2 (volume.restrict (Icc (-L) L))) x) =ᵐ[volume] (0 : ℝ → ℂ) := by
    have hz0 := extend_congr_ae (Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (-L) L)))
    simpa [RHFormDomain.extend] using hz0
  exact hn (MeasureTheory.Measure.eq_of_ae_eq (he.symm.trans he0) hf continuous_zero)

end RHTestRestriction
