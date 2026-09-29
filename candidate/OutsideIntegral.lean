import RealAutocorr
open MeasureTheory Set
namespace RHExternalPotential
open RH_Rebaseline

lemma outside_right {L x : ℝ} (hx : x < L) :
    IntegrableOn (fun y => K_kernel |x-y|) (Ioi L) ∧
      (∫ y in Ioi L, K_kernel |x-y|) = T_tail (L-x) := by
  have hp : 0 < L-x := sub_pos.mpr hx
  have hpre : (fun y : ℝ => y-x) ⁻¹' Ioi (L-x) = Ioi L := by
    ext y
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have hm := measurePreserving_sub_right volume x
  have he : MeasurableEmbedding (fun y : ℝ => y-x) :=
    (IsometryEquiv.subRight x).toHomeomorph.measurableEmbedding
  have hi := (hm.integrableOn_comp_preimage he).mpr (integrableOn_Ioi_K_kernel hp)
  rw [hpre] at hi
  have heq : EqOn (fun y : ℝ => K_kernel (y-x)) (fun y => K_kernel |x-y|) (Ioi L) := by
    intro y hy
    have hxy : x-y ≤ 0 := by have : L < y := hy; linarith
    dsimp only
    rw [abs_of_nonpos hxy]
    congr 1
    ring
  refine ⟨hi.congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq]
  have hh := hm.setIntegral_preimage_emb he K_kernel (Ioi (L-x))
  rw [hpre] at hh
  exact hh.trans (integral_Ioi_K_kernel_eq_T_tail hp)

lemma outside_left {L x : ℝ} (hx : -L < x) :
    IntegrableOn (fun y => K_kernel |x-y|) (Iio (-L)) ∧
      (∫ y in Iio (-L), K_kernel |x-y|) = T_tail (L+x) := by
  have hp : 0 < L+x := by linarith
  have hpre : (fun y : ℝ => x-y) ⁻¹' Ioi (L+x) = Iio (-L) := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  have hm := volume.measurePreserving_sub_left x
  have he : MeasurableEmbedding (fun y : ℝ => x-y) :=
    (IsometryEquiv.subLeft x).toHomeomorph.measurableEmbedding
  have hi := (hm.integrableOn_comp_preimage he).mpr (integrableOn_Ioi_K_kernel hp)
  rw [hpre] at hi
  have heq : EqOn (fun y : ℝ => K_kernel (x-y)) (fun y => K_kernel |x-y|) (Iio (-L)) := by
    intro y hy
    have hxy : 0 ≤ x-y := by have : y < -L := hy; linarith
    dsimp only
    rw [abs_of_nonneg hxy]
  refine ⟨hi.congr_fun heq measurableSet_Iio, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Iio heq]
  have hh := hm.setIntegral_preimage_emb he K_kernel (Ioi (L+x))
  rw [hpre] at hh
  exact hh.trans (integral_Ioi_K_kernel_eq_T_tail hp)

theorem outside_integral {L x : ℝ} (hx : |x| < L) :
    IntegrableOn (fun y => K_kernel |x-y|) ((Icc (-L) L)ᶜ) ∧
      (∫ y in (Icc (-L) L)ᶜ, K_kernel |x-y|) = T_tail (L-x) + T_tail (L+x) := by
  obtain ⟨hxl, hxr⟩ := abs_lt.mp hx
  obtain ⟨hir, her⟩ := outside_right hxr
  obtain ⟨hil, hel⟩ := outside_left hxl
  have hset : (Icc (-L) L)ᶜ = Ioi L ∪ Iio (-L) := by
    ext y
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Ioi, mem_Iio, not_and_or, not_le]
    tauto
  have hd : Disjoint (Ioi L) (Iio (-L)) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hL : 0 < L := lt_of_le_of_lt (abs_nonneg x) hx
    have hy' : L < y := hy
    have hz' : y < -L := hz
    linarith
  rw [hset]
  exact ⟨hir.union hil, (setIntegral_union hd measurableSet_Iio hir hil).trans (by rw [her, hel])⟩

end RHExternalPotential
