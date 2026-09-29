import Caps0494

/-! # 0494 T3: reduction of `G6c` to explicit approximation integrals

The residual `col - project o 64 col` is the orthogonal residual onto the 64 orthonormal
directions `embed (basis (degree o k))`, so any coefficients `W` give an upper bound
(best approximation). Hence `G6c concrete k` follows from an explicit integral inequality
with arbitrary fixed coefficients `W` (e.g. 0417's `C·B`). -/

open MeasureTheory Set
open scoped BigOperators Matrix

namespace RHResidualApprox0494
open RHConditionalLog5 RHResidualCertificate RHResidualMembership

/-- Best approximation by an orthonormal finite family in a real inner product space. -/
lemma best_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ℕ) (e : ℕ → E)
    (he : ∀ m ∈ s, ∀ n ∈ s, inner ℝ (e m) (e n) = if m = n then (1:ℝ) else 0)
    (x : E) (c : ℕ → ℝ) :
    ‖x - ∑ k ∈ s, inner ℝ (e k) x • e k‖ ≤ ‖x - ∑ k ∈ s, c k • e k‖ := by
  set y := x - ∑ k ∈ s, inner ℝ (e k) x • e k with hy
  set d := ∑ k ∈ s, (inner ℝ (e k) x - c k) • e k with hd
  have hsplit : x - ∑ k ∈ s, c k • e k = y + d := by
    simp only [hy, hd, sub_smul, Finset.sum_sub_distrib]
    abel
  have horth : ∀ m ∈ s, inner ℝ y (e m) = 0 := by
    intro m hm
    simp only [hy, inner_sub_left, sum_inner, inner_smul_left, RCLike.conj_to_real]
    have hsum : ∑ k ∈ s, inner ℝ (e k) x * inner ℝ (e k) (e m) = inner ℝ (e m) x := by
      rw [Finset.sum_eq_single m]
      · rw [he m hm m hm, if_pos rfl, mul_one]
      · intro k hk hkm; rw [he k hk m hm, if_neg hkm, mul_zero]
      · intro h; exact absurd hm h
    rw [hsum, real_inner_comm]
    ring
  have hyd : inner ℝ y d = 0 := by
    simp only [hd, inner_sum, inner_smul_right]
    exact Finset.sum_eq_zero (fun m hm => by rw [horth m hm, mul_zero])
  have hsq : ‖y‖ ^ 2 ≤ ‖y + d‖ ^ 2 := by
    rw [norm_add_sq_real, hyd]
    nlinarith [sq_nonneg ‖d‖]
  rw [hsplit]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2:ℕ) ≠ 0)).mp hsq

lemma degree_inj (o : Bool) {m n : ℕ} : degree o m = degree o n ↔ m = n := by
  unfold degree; constructor <;> intro h <;> [skip; rw [h]] <;> split at h <;> omega

lemma e_orthonormal (o : Bool) :
    ∀ m ∈ Finset.range 64, ∀ n ∈ Finset.range 64,
      inner ℝ (embed (basis (degree o m))) (embed (basis (degree o n))) = if m = n then (1:ℝ) else 0 := by
  intro m _ n _
  rw [RHBandNorm.basis_inner]
  simp only [degree_inj]

lemma col_memLp (o : Bool) (i : I) : MemLp (col o i) 2 volume := (RHG2Final0489.g2.1 o i).1

lemma columnResidual_eq (o : Bool) (i : I) :
    columnResidual o i = embed (col o i) -
      ∑ k ∈ Finset.range 64, inner ℝ (embed (basis (degree o k))) (embed (col o i)) •
        embed (basis (degree o k)) := by
  have hp : MemLp (project o 64 (col o i)) 2 volume := project_memLp o 64 (col o i)
  unfold columnResidual
  rw [RHBandNorm.embed_sub _ _ (col_memLp o i) hp, RHStepA2G2.embed_project_64]
  refine congrArg (HSub.hSub (embed (col o i))) ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [RHBandNorm.inner_embed _ _ (basis_memLp _) (col_memLp o i)]
  rfl

lemma transformed_eq (o : Bool) (j : I) :
    transformedResidual (columnResidual o) (RHConcreteParameters.concrete.B o) j =
      (∑ i : I, RHConcreteParameters.concrete.B o i j • embed (col o i)) -
      ∑ k ∈ Finset.range 64,
        inner ℝ (embed (basis (degree o k)))
          (∑ i : I, RHConcreteParameters.concrete.B o i j • embed (col o i)) •
        embed (basis (degree o k)) := by
  unfold transformedResidual
  simp only [columnResidual_eq, smul_sub, Finset.sum_sub_distrib, inner_sum, inner_smul_right,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range 64)]

lemma approx_embed (o : Bool) (W : ℕ → I → ℝ) (j : I) :
    (∑ i : I, RHConcreteParameters.concrete.B o i j • embed (col o i)) -
      ∑ k ∈ Finset.range 64, W k j • embed (basis (degree o k)) =
    embed (fun x => ∑ i : I, RHConcreteParameters.concrete.B o i j * col o i x -
      ∑ k ∈ Finset.range 64, W k j * basis (degree o k) x) := by
  have h1 : ∀ i : I, MemLp (RHConcreteParameters.concrete.B o i j • col o i) 2 volume :=
    fun i => (col_memLp o i).const_smul _
  have h2 : ∀ k : ℕ, MemLp (W k j • basis (degree o k)) 2 volume :=
    fun k => (basis_memLp _).const_smul _
  have hf : (fun x => ∑ i : I, RHConcreteParameters.concrete.B o i j * col o i x -
      ∑ k ∈ Finset.range 64, W k j * basis (degree o k) x) =
      (∑ i : I, RHConcreteParameters.concrete.B o i j • col o i) -
        ∑ k ∈ Finset.range 64, W k j • basis (degree o k) := by
    funext x; simp [Finset.sum_apply]
  rw [hf, RHBandNorm.embed_sub _ _ (memLp_finsetSum' _ (fun i _ => h1 i))
      (memLp_finsetSum' _ (fun k _ => h2 k)),
    RHBandNorm.embed_sum _ _ h1, RHBandNorm.embed_sum _ _ h2,
    Finset.sum_congr rfl (fun i _ => RHBandNorm.embed_smul _ _ (col_memLp o i)),
    Finset.sum_congr rfl (fun k _ => RHBandNorm.embed_smul _ _ (basis_memLp (degree o k)))]

lemma approx_memLp (o : Bool) (W : ℕ → I → ℝ) (j : I) :
    MemLp (fun x => ∑ i : I, RHConcreteParameters.concrete.B o i j * col o i x -
      ∑ k ∈ Finset.range 64, W k j * basis (degree o k) x) 2 volume := by
  have h1 := memLp_finsetSum' (Finset.univ : Finset I)
    (fun i _ => (col_memLp o i).const_mul (RHConcreteParameters.concrete.B o i j))
  have h2 := memLp_finsetSum' (Finset.range 64)
    (fun k _ => (basis_memLp (degree o k)).const_mul (W k j))
  convert h1.sub h2 using 1
  funext x; simp [Finset.sum_apply]

/-- **Finite reduction of G6.** Any fixed coefficients `W` give `G6c` from explicit integrals. -/
theorem G6c_of_approx (k : RHCaps0494.Caps) (W : Bool → ℕ → I → ℝ)
    (h : ∀ o : Bool, (1 / dM o) * ∑ j : I, ∫ x,
      (∑ i : I, RHConcreteParameters.concrete.B o i j * col o i x -
        ∑ m ∈ Finset.range 64, W o m j * basis (degree o m) x) ^ 2 ≤ k.tau o) :
    RHCaps0494.G6c RHConcreteParameters.concrete k := by
  intro o
  rw [RHStepB2G6.trace_smul_transformed_trace]
  refine le_trans ?_ (h o)
  apply mul_le_mul_of_nonneg_left _ (by have := dM_pos o; positivity)
  apply Finset.sum_le_sum
  intro j _
  have hb := best_approx (Finset.range 64) (fun k => embed (basis (degree o k))) (e_orthonormal o)
    (∑ i : I, RHConcreteParameters.concrete.B o i j • embed (col o i)) (fun m => W o m j)
  rw [← transformed_eq, approx_embed] at hb
  rw [← RHStepA1G1.embed_norm_sq _ (approx_memLp o (W o) j)]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end RHResidualApprox0494

