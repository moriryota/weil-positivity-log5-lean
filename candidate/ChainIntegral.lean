import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic
open MeasureTheory Set
open scoped ENNReal
namespace RHChainIntegral

lemma ico_split (g : ℝ → ℝ≥0∞) {s m e : ℝ} (hsm : s ≤ m) (hme : m ≤ e) :
    (∫⁻ t in Ico s e, g t) = (∫⁻ t in Ico s m, g t) + (∫⁻ t in Ico m e, g t) := by
  rw [← Ico_union_Ico_eq_Ico hsm hme]
  exact lintegral_union measurableSet_Ico Ico_disjoint_Ico_same

lemma ico_shift (g : ℝ → ℝ≥0∞) (s e d : ℝ) :
    (∫⁻ t in Ico s e, g (t+d)) = ∫⁻ t in Ico (s+d) (e+d), g t := by
  have hp : (fun t : ℝ => t+d) ⁻¹' Ico (s+d) (e+d) = Ico s e := by
    ext t
    simp only [mem_preimage, mem_Ico, add_le_add_iff_right, add_lt_add_iff_right]
  have he := (Homeomorph.addRight d).measurableEmbedding
  have hm := (measurePreserving_add_right volume d).restrict_preimage_emb he (Ico (s+d) (e+d))
  have h := hm.lintegral_comp_emb he g
  rw [hp] at h
  exact h

theorem chain_split (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {s W a : ℝ} (ha : 0 < a) (h2 : 2*a ≤ W) (h3 : W ≤ 3*a) :
    (∫⁻ t in Ico s (s+W), g t) =
      (∫⁻ t in Ico s (s+W-2*a), g t + g (t+a) + g (t+2*a)) +
      (∫⁻ t in Ico (s+W-2*a) (s+a), g t + g (t+a)) := by
  have hs1 := ico_shift g s (s+a) a
  rw [show s+a+a = s+2*a by ring] at hs1
  have hs2 := ico_shift g s (s+W-2*a) (2*a)
  rw [show s+W-2*a+2*a = s+W by ring] at hs2
  have hfull : (∫⁻ t in Ico s (s+W), g t) =
      ((∫⁻ t in Ico s (s+a), g t) + (∫⁻ t in Ico s (s+a), g (t+a))) +
        (∫⁻ t in Ico s (s+W-2*a), g (t+2*a)) := by
    rw [ico_split g (m := s+2*a) (by linarith) (by linarith),
      ico_split g (s := s) (m := s+a) (e := s+2*a) (by linarith) (by linarith), hs1, hs2]
  have hbase := ico_split (fun t => g t + g (t+a))
    (s := s) (m := s+W-2*a) (e := s+a) (by linarith) (by linarith)
  have hga : Measurable (fun t : ℝ => g (t+a)) := hg.comp (by fun_prop)
  have hsum : Measurable (fun t : ℝ => g t + g (t+a)) := hg.add hga
  rw [hfull, ← lintegral_add_left hg _, hbase,
    lintegral_add_left hsum _]
  ac_rfl

end RHChainIntegral
