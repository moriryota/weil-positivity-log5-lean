import ChainIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
open MeasureTheory Set
namespace RHShiftChain

lemma ico_split (g : ℝ → ℝ) {s m e : ℝ} (hsm : s ≤ m) (hme : m ≤ e)
    (hg : IntegrableOn g (Ico s e)) :
    (∫ t in Ico s e, g t) = (∫ t in Ico s m, g t) + (∫ t in Ico m e, g t) := by
  have hi1 := hg.mono_set (Ico_subset_Ico le_rfl hme)
  have hi2 := hg.mono_set (Ico_subset_Ico hsm le_rfl)
  rw [← Ico_union_Ico_eq_Ico hsm hme]
  exact setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico hi1 hi2

lemma ico_shift (g : ℝ → ℝ) (s e d : ℝ) :
    (∫ t in Ico s e, g (t+d)) = ∫ t in Ico (s+d) (e+d), g t := by
  have hp : (fun t : ℝ => t+d) ⁻¹' Ico (s+d) (e+d) = Ico s e := by
    ext t
    simp only [mem_preimage, mem_Ico, add_le_add_iff_right, add_lt_add_iff_right]
  have he := (Homeomorph.addRight d).measurableEmbedding
  have h := (measurePreserving_add_right volume d).setIntegral_preimage_emb he g (Ico (s+d) (e+d))
  rw [hp] at h
  exact h

lemma ico_shift_integrable (g : ℝ → ℝ) (s e d : ℝ) :
    IntegrableOn (fun t => g (t+d)) (Ico s e) ↔ IntegrableOn g (Ico (s+d) (e+d)) := by
  have hp : (fun t : ℝ => t+d) ⁻¹' Ico (s+d) (e+d) = Ico s e := by
    ext t
    simp only [mem_preimage, mem_Ico, add_le_add_iff_right, add_lt_add_iff_right]
  have he := (Homeomorph.addRight d).measurableEmbedding
  have h := (measurePreserving_add_right volume d).integrableOn_comp_preimage he (f := g)
    (s := Ico (s+d) (e+d))
  rw [hp] at h
  exact h

theorem adjacent_chain (g : ℝ → ℝ) {s W a : ℝ}
    (ha : 0 < a) (h2 : 2*a ≤ W) (h3 : W ≤ 3*a)
    (hg : IntegrableOn g (Ico s (s+W-a))) :
    (∫ t in Ico s (s+W-a), g t) =
      (∫ t in Ico s (s+W-2*a), g t + g (t+a)) +
      (∫ t in Ico (s+W-2*a) (s+a), g t) := by
  have hb : IntegrableOn g (Ico s (s+a)) :=
    hg.mono_set (Ico_subset_Ico le_rfl (by linarith))
  have ht : IntegrableOn g (Ico s (s+W-2*a)) :=
    hg.mono_set (Ico_subset_Ico le_rfl (by linarith))
  have hts : IntegrableOn (fun t => g (t+a)) (Ico s (s+W-2*a)) := by
    apply (ico_shift_integrable g _ _ _).mpr
    apply hg.mono_set
    apply Ico_subset_Ico <;> linarith
  have hsh := ico_shift g s (s+W-2*a) a
  rw [show s+W-2*a+a = s+W-a by ring] at hsh
  rw [ico_split g (m := s+a) (by linarith) (by linarith) hg,
    ico_split g (m := s+W-2*a) (by linarith) (by linarith) hb,
    integral_add ht hts, hsh]
  ring

theorem adjacent_product_chain (f : ℝ → ℝ) {s W a : ℝ}
    (ha : 0 < a) (h2 : 2*a ≤ W) (h3 : W ≤ 3*a)
    (hf : IntegrableOn (fun t => f t * f (t+a)) (Ico s (s+W-a))) :
    (∫ t in Ico s (s+W-a), f t * f (t+a)) =
      (∫ t in Ico s (s+W-2*a), f t * f (t+a) + f (t+a) * f (t+2*a)) +
      (∫ t in Ico (s+W-2*a) (s+a), f t * f (t+a)) := by
  have h := adjacent_chain (fun t => f t * f (t+a)) ha h2 h3 hf
  have hid (t : ℝ) : t+a+a = t+2*a := by ring
  simpa only [hid] using h

theorem weighted_product_chain (f : ℝ → ℝ) (alpha beta : ℝ) {s W a : ℝ}
    (ha : 0 < a) (h2 : 2*a ≤ W) (h3 : W ≤ 3*a)
    (hf : IntegrableOn (fun t => f t * f (t+a)) (Ico s (s+W-a)))
    (hf2 : IntegrableOn (fun t => f t * f (t+2*a)) (Ico s (s+W-2*a))) :
    2*alpha*(∫ t in Ico s (s+W-a), f t * f (t+a)) +
      2*beta*(∫ t in Ico s (s+W-2*a), f t * f (t+2*a)) =
    (∫ t in Ico s (s+W-2*a),
      2*alpha*(f t*f (t+a) + f (t+a)*f (t+2*a)) + 2*beta*(f t*f (t+2*a))) +
    (∫ t in Ico (s+W-2*a) (s+a), 2*alpha*(f t*f (t+a))) := by
  have ht : IntegrableOn (fun t => f t*f (t+a)) (Ico s (s+W-2*a)) :=
    hf.mono_set (Ico_subset_Ico le_rfl (by linarith))
  have hts : IntegrableOn (fun t => f (t+a)*f (t+2*a)) (Ico s (s+W-2*a)) := by
    have h := (ico_shift_integrable (fun t => f t*f (t+a)) s (s+W-2*a) a).mpr
      (hf.mono_set (Ico_subset_Ico (by linarith) (by linarith)))
    have hid (t : ℝ) : t+a+a = t+2*a := by ring
    simpa only [hid] using h
  have hsum : IntegrableOn (fun t => f t*f (t+a) + f (t+a)*f (t+2*a))
      (Ico s (s+W-2*a)) := ht.add hts
  rw [integral_add (hsum.const_mul (2*alpha)) (hf2.const_mul (2*beta))]
  simp only [integral_const_mul]
  rw [adjacent_product_chain f ha h2 h3 hf]
  ring

end RHShiftChain

