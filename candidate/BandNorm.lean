import RealLowZero
open MeasureTheory Set
open scoped BigOperators
namespace RHBandNorm
open RHConditionalLog5 RHResidualMembership RHRealLowZero
lemma embed_add (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    embed (f+g) = embed f + embed g := by
  simp only [embed, dif_pos hf, dif_pos hg, dif_pos (hf.add hg)]
  rfl
lemma embed_sub (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    embed (f-g) = embed f - embed g := by
  simp only [embed, dif_pos hf, dif_pos hg, dif_pos (hf.sub hg)]
  rfl
lemma embed_smul (a : ℝ) (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    embed (a • f) = a • embed f := by
  simp only [embed, dif_pos hf, dif_pos (hf.const_smul a)]
  rfl
lemma embed_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 volume) :
    embed (∑ i ∈ s, f i) = ∑ i ∈ s, embed (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [embed]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      embed_add _ _ (hf i) (memLp_finsetSum' s (fun j _ => hf j)), ih]
lemma inner_embed (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (embed f) (embed g) = ∫ x, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have he (u : ℝ → ℝ) (hu : MemLp u 2 volume) :
      (embed u : ℝ → ℝ) =ᵐ[volume] u := by
    simpa only [embed, dif_pos hu] using hu.coeFn_toLp
  filter_upwards [he f hf, he g hg] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]
lemma basis_inner (m n : ℕ) :
    inner ℝ (embed (basis m)) (embed (basis n)) = if m=n then 1 else 0 := by
  rw [inner_embed _ _ (basis_memLp m) (basis_memLp n)]
  exact coeff_basis n m
lemma basis_inner_function (n : ℕ) (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    inner ℝ (embed (basis n)) (embed f) = coeff f n :=
  inner_embed _ _ (basis_memLp n) hf

/-- Finite projection identity. No completeness assumption is used. -/
lemma projection_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (f : E)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i=j then 1 else 0) :
    (∑ i, (inner ℝ (v i) f)^2) +
      ‖f - ∑ i, (inner ℝ (v i) f) • v i‖^2 = ‖f‖^2 := by
  let p := ∑ i, (inner ℝ (v i) f) • v i
  have hfp : inner ℝ f p = ∑ i, (inner ℝ (v i) f)^2 := by
    simp only [p, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm f (v i)]
    ring
  have hp : inner ℝ p p = ∑ i, (inner ℝ (v i) f)^2 := by
    simp only [p, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hv]
    simp [pow_two]
  have hn := norm_sub_sq_real f p
  rw [hfp, ← real_inner_self_eq_norm_sq p, hp] at hn
  change (∑ i, (inner ℝ (v i) f)^2) + ‖f-p‖^2 = ‖f‖^2
  linarith

theorem band_far_norm (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∑ i : I, (band o u i)^2) + ‖far o u‖^2 = ‖embed (tail o u)‖^2 := by
  let v : I → H := fun i => embed (basis (degree o (32+i)))
  have hi (i : I) : inner ℝ (v i) (embed (tail o u)) = band o u i :=
    basis_inner_function _ _ (tail_memLp o u hu)
  have hv (i j : I) : inner ℝ (v i) (v j) = if i=j then 1 else 0 := by
    dsimp [v]
    rw [basis_inner]
    have he : degree o (32+i) = degree o (32+j) ↔ i=j := by
      constructor
      · intro h; apply Fin.ext; unfold degree at h; omega
      · intro h; rw [h]
    simp [he]
  have hfar : far o u = embed (tail o u) - ∑ i : I, band o u i • v i := by
    unfold far
    rw [embed_sub _ _ (tail_memLp o u hu)
      (memLp_finsetSum' (Finset.univ : Finset I) (fun i _ =>
        (basis_memLp (degree o (32+i))).const_smul (band o u i)))]
    rw [embed_sum _ _ (fun (i : I) => (basis_memLp (degree o (32+i))).const_smul (band o u i))]
    simp only [embed_smul _ _ (basis_memLp _)]
    rfl
  have h := projection_norm v (embed (tail o u)) hv
  simp_rw [hi] at h
  rw [← hfar] at h
  exact h
end RHBandNorm
