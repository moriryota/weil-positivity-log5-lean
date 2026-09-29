import RawProjection
open Set
namespace RHRawProjection

lemma seed_of_mem {L a r : ℝ} (u : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Ico (-L) (L-2*a)) :
    seed L a r u t = RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a)) :=
  indicator_of_mem ht _

lemma seed_of_not_mem {L a r : ℝ} (u : ℝ → ℝ) {t : ℝ}
    (ht : t ∉ Ico (-L) (L-2*a)) : seed L a r u t = 0 :=
  indicator_of_notMem ht _

lemma triple_seed_vanish {L a r : ℝ} (u : ℝ → ℝ) (ha : 0 < a)
    (h3 : 2*L ≤ 3*a) {t : ℝ} (ht : t ∈ Ico (-L) (L-2*a)) :
    seed L a r u (t-a) = 0 ∧ seed L a r u (t-2*a) = 0 ∧
      seed L a r u (t+a) = 0 ∧ seed L a r u (t+2*a) = 0 := by
  rcases ht with ⟨htl,htr⟩
  constructor
  · apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.1]
  constructor
  · apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.1]
  constructor
  · apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.2]
  · apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.2]

theorem project_triple_left {L a r : ℝ} (u : ℝ → ℝ) (ha : 0 < a)
    (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) {t : ℝ} (ht : t ∈ Ico (-L) (L-2*a)) :
    project L a r u t = RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a)) := by
  obtain ⟨hm1,hm2,hp1,hp2⟩ := triple_seed_vanish (r := r) u ha h3 ht
  simp only [project, hm1, hm2, mul_zero, add_zero, seed_of_mem u ht]

theorem project_triple_middle {L a r : ℝ} (u : ℝ → ℝ) (ha : 0 < a)
    (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) {t : ℝ} (ht : t ∈ Ico (-L) (L-2*a)) :
    project L a r u (t+a) = r * RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a)) := by
  obtain ⟨hm1,hm2,hp1,hp2⟩ := triple_seed_vanish (r := r) u ha h3 ht
  have he1 : t+a-a = t := by ring
  have he2 : t+a-2*a = t-a := by ring
  simp only [project, he1, he2, hp1, hm1, add_zero, zero_add, seed_of_mem u ht]

theorem project_triple_right {L a r : ℝ} (u : ℝ → ℝ) (ha : 0 < a)
    (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) {t : ℝ} (ht : t ∈ Ico (-L) (L-2*a)) :
    project L a r u (t+2*a) = RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a)) := by
  obtain ⟨hm1,hm2,hp1,hp2⟩ := triple_seed_vanish (r := r) u ha h3 ht
  have he1 : t+2*a-a = t+a := by ring
  have he2 : t+2*a-2*a = t := by ring
  simp only [project, he1, he2, hp1, hp2, mul_zero, zero_add, seed_of_mem u ht]

theorem project_double_zero {L a r : ℝ} (u : ℝ → ℝ) (ha : 0 < a)
    (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) {t : ℝ} (ht : t ∈ Ico (L-2*a) (-L+a)) :
    project L a r u t = 0 ∧ project L a r u (t+a) = 0 := by
  rcases ht with ⟨htl,htr⟩
  have hz : seed L a r u t = 0 := by
    apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.2]
  have hm1 : seed L a r u (t-a) = 0 := by
    apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.1]
  have hm2 : seed L a r u (t-2*a) = 0 := by
    apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.1]
  have hp1 : seed L a r u (t+a) = 0 := by
    apply seed_of_not_mem
    simp only [mem_Ico]
    intro h
    linarith [h.2]
  have he1 : t+a-a = t := by ring
  have he2 : t+a-2*a = t-a := by ring
  simp only [project, he1, he2, hz, hm1, hm2, hp1, mul_zero, add_zero, and_self]

end RHRawProjection
