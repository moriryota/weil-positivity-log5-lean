import FinalAll0524
/-! # 0579: uniform lower bound, existence version

`∃ c > 0, ∀ f` (C², support in [-log 5 / 2, log 5 / 2]), `c ∫ ‖f‖² ≤ Re W(f,f)`.
Inputs: the existing gates G1–G4, G5c, G6c for `RHConcreteParameters.concrete` with
`RHT5Final0512.capsNew`. No new numerical check, no new positivity hypothesis.
Separate module; the existing development is not modified. -/
set_option linter.all false
open MeasureTheory
open scoped BigOperators Matrix
namespace RHUniform0579
open RHConditionalLog5 RHTargetFormBinding RHResidualCertificate

/-! ## Definitions -/

/-- Band coupling matrix, oriented by the canonical `mixed`. -/
noncomputable def At (o : Bool) : Matrix I I ℝ :=
  fun i j => ∫ x, col o j x * basis (degree o (32+i)) x

theorem mixed_eq_At_mulVec (o : Bool) (u : ℝ → ℝ) :
    mixed o u = At o *ᵥ alpha o u := by
  funext i
  simp [mixed, At, Matrix.mulVec, dotProduct, mul_comm]

/-- Squared Frobenius norm (a finite sum; no numerical value is computed). -/
noncomputable def frob (M : Matrix I I ℝ) : ℝ := ∑ i, ∑ j, (M i j)^2

/-- `D = max 1 ‖B‖_F²`. -/
noncomputable def Dc (P : Parameters) (o : Bool) : ℝ := max 1 (frob (P.B o))
/-- `κ = ‖A_t B‖_F² / d_N`. -/
noncomputable def kappa (P : Parameters) (o : Bool) : ℝ := frob (At o * P.B o) / dN o
/-- `ε = δ / (2 (a + κ))` with the capsNew values `a = 999/1000`, `δ = 9/1000`. -/
noncomputable def eps (P : Parameters) (o : Bool) : ℝ := (9/1000) / (2 * (999/1000 + kappa P o))
/-- `c₀ = min (δ / (2D)) (ε d_N)`. -/
noncomputable def c0 (P : Parameters) (o : Bool) : ℝ :=
  min ((9/1000) / (2 * Dc P o)) (eps P o * dN o)

/-! ## Elementary facts -/

lemma frob_nonneg (M : Matrix I I ℝ) : 0 ≤ frob M :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma mulVec_sq_le (M : Matrix I I ℝ) (x : I → ℝ) :
    ∑ i, ((M *ᵥ x) i)^2 ≤ frob M * ∑ j, (x j)^2 := by
  unfold frob
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simpa [Matrix.mulVec, dotProduct] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) x

lemma kappa_nonneg (P : Parameters) (o : Bool) : 0 ≤ kappa P o :=
  div_nonneg (frob_nonneg _) (dN_pos o).le

lemma Dc_pos (P : Parameters) (o : Bool) : 0 < Dc P o :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

lemma eps_pos (P : Parameters) (o : Bool) : 0 < eps P o := by
  have := kappa_nonneg P o
  unfold eps; apply div_pos (by norm_num); linarith

lemma one_sub_eps (P : Parameters) (o : Bool) :
    1 - eps P o = (2000 * kappa P o + 1989) / (2000 * kappa P o + 1998) := by
  have hk := kappa_nonneg P o
  have h1 : (2 * (999/1000 + kappa P o)) ≠ 0 := by positivity
  have h2 : (2000 * kappa P o + 1998) ≠ 0 := by positivity
  unfold eps
  field_simp
  ring

lemma eps_lt_one (P : Parameters) (o : Bool) : eps P o < 1 := by
  have hk := kappa_nonneg P o
  have h := one_sub_eps P o
  have : 0 < (2000 * kappa P o + 1989) / (2000 * kappa P o + 1998) := by positivity
  linarith

lemma c0_pos (P : Parameters) (o : Bool) : 0 < c0 P o := by
  unfold c0
  exact lt_min (div_pos (by norm_num) (by linarith [Dc_pos P o]))
    (mul_pos (eps_pos P o) (dN_pos o))

/-- The coefficient identity behind the choice of `ε`. -/
lemma coef_bound (P : Parameters) (o : Bool) :
    (9/1000:ℝ) / 2 ≤ 999/1000 - (1 / (1 - eps P o) - 1) * kappa P o
      - 1 / (1 - eps P o) * (99/100) := by
  have hk := kappa_nonneg P o
  have hD : 0 < 2000 * kappa P o + 1989 := by linarith
  have hN : 0 < 2000 * kappa P o + 1998 := by linarith
  rw [one_sub_eps P o, one_div_div]
  have key : 999/1000 - ((2000 * kappa P o + 1998) / (2000 * kappa P o + 1989) - 1) * kappa P o
      - (2000 * kappa P o + 1998) / (2000 * kappa P o + 1989) * (99/100) - (9/1000:ℝ)/2
      = (81/2000) / (2000 * kappa P o + 1989) := by
    field_simp
    ring
  have hp : 0 < (81/2000:ℝ) / (2000 * kappa P o + 1989) := by positivity
  linarith

/-! ## ε-completion of squares -/

lemma scalar_eps {w ε m b : ℝ} (hw : 0 < w) (he : ε < 1) :
    -(m^2 / ((1-ε)*w)) + ε*w*b^2 ≤ 2*m*b + w*b^2 := by
  have ht : 0 < (1-ε)*w := mul_pos (by linarith) hw
  have h : 0 ≤ ((1-ε)*w*b + m)^2 / ((1-ε)*w) := div_nonneg (sq_nonneg _) ht.le
  have hexp : ((1-ε)*w*b + m)^2 / ((1-ε)*w) = (1-ε)*w*b^2 + 2*m*b + m^2/((1-ε)*w) := by
    rw [add_sq, add_div, add_div, mul_pow]
    have hne : ((1-ε)*w) ≠ 0 := ht.ne'
    have hne1 : (1-ε) ≠ 0 := by linarith
    have hw0 : w ≠ 0 := hw.ne'
    congr 1
    congr 1
    · field_simp
    · field_simp
  linarith

lemma hilbert_eps {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r z : E) {dM ε : ℝ} (hd : 0 < dM) (he : ε < 1) :
    -(‖r‖^2 / ((1-ε)*dM)) + ε*dM*‖z‖^2 ≤ 2 * inner ℝ r z + dM*‖z‖^2 := by
  have h1 := scalar_eps (m := -‖r‖) (b := ‖z‖) hd he
  have h2 : -(‖r‖*‖z‖) ≤ inner ℝ r z := by
    have := abs_real_inner_le_norm r z
    linarith [neg_abs_le (inner ℝ r z)]
  rw [neg_sq] at h1
  linarith

/-! ## U-L6: quantitative Schur bound at fixed parity (capsNew) -/

theorem component_quantitative (P : Parameters)
    (h1 : G1 P) (h2 : G2 P) (h3 : G3 P) (h4 : G4 P)
    (h5 : RHCaps0494.G5c P RHT5Final0512.capsNew)
    (h6 : RHCaps0494.G6c P RHT5Final0512.capsNew)
    (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (9/1000:ℝ)/2 * (∑ i : I, (P.coordinates o u i)^2) +
      eps P o * dN o * ‖embed (tail o u)‖^2 ≤ targetQ_real (component o u) := by
  set ε := eps P o with hεdef
  set S := ∑ i : I, (P.coordinates o u i)^2 with hSdef
  set r := residual_vector (columnResidual o) (P.B o *ᵥ P.coordinates o u) with hr
  set z := far o u with hz
  set X := ∑ i : I, (mixed o u i)^2 / P.weights o i with hX
  set g := 1 / (1 - ε) with hg
  have hε0 : 0 < ε := eps_pos P o
  have hε1 : ε < 1 := eps_lt_one P o
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hw : ∀ i, 0 < P.weights o i := fun i => (dN_pos o).trans_le ((h4 o).1 i)
  have hdM := dM_pos o
  have hdN := dN_pos o
  -- Schur input
  have hQ := schur_input P h1 h2 h3 h4 o u hu
  -- ε-completion, band
  have hsum : ∑ i : I, (-((mixed o u i)^2 / ((1-ε) * P.weights o i)) + ε * P.weights o i * (band o u i)^2)
      ≤ ∑ i : I, (2 * mixed o u i * band o u i + P.weights o i * (band o u i)^2) :=
    Finset.sum_le_sum (fun i _ => scalar_eps (hw i) hε1)
  have hsplit : ∑ i : I, (-((mixed o u i)^2 / ((1-ε) * P.weights o i)) + ε * P.weights o i * (band o u i)^2)
      = -(g * X) + ε * ∑ i : I, P.weights o i * (band o u i)^2 := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hX, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1; refine Finset.sum_congr rfl (fun i _ => ?_); rw [hg, div_mul_div_comm, one_mul]
    · refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- ε-completion, far
  have hH := hilbert_eps r z hdM hε1
  have hHg : ‖r‖^2 / ((1-ε) * dM o) = g * (‖r‖^2 / dM o) := by rw [hg, div_mul_div_comm, one_mul]
  -- G5c
  have hLow : (1 - 1/1000) * S ≤ targetQ_real (low o u) - X := by
    have := h5 o u hu
    simpa [RHT5Final0512.capsNew] using this
  -- G6c: residual bound
  have hRes : ‖r‖^2 / dM o ≤ 99/100 * S := by
    have := residual_bound_of_gram_trace (columnResidual o) (P.B o) (P.coordinates o u) hdM
      (h6 o) rfl
    simpa [RHT5Final0512.capsNew] using this
  -- mixed bound
  have hα : P.B o *ᵥ P.coordinates o u = alpha o u := (h3 o u hu).1
  have hm : mixed o u = (At o * P.B o) *ᵥ P.coordinates o u := by
    rw [mixed_eq_At_mulVec, ← hα, Matrix.mulVec_mulVec]
  have hMsq : ∑ i : I, (mixed o u i)^2 ≤ frob (At o * P.B o) * S := by
    rw [hm]; exact mulVec_sq_le _ _
  have hXle : X ≤ kappa P o * S := by
    have h1' : X ≤ ∑ i : I, (mixed o u i)^2 / dN o :=
      Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) hdN ((h4 o).1 i))
    have h2' : ∑ i : I, (mixed o u i)^2 / dN o = (∑ i : I, (mixed o u i)^2) / dN o := by
      rw [Finset.sum_div]
    have h3' : (∑ i : I, (mixed o u i)^2) / dN o ≤ frob (At o * P.B o) * S / dN o :=
      div_le_div_of_nonneg_right hMsq hdN.le
    have h4' : frob (At o * P.B o) * S / dN o = kappa P o * S := by
      unfold kappa; ring
    linarith
  -- g ≥ 1
  have hg1 : 1 ≤ g := by
    rw [hg, le_div_iff₀ (by linarith)]; linarith
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)
  have hF5 := mul_le_mul_of_nonneg_left hXle (by linarith : (0:ℝ) ≤ g - 1)
  have hF6 := mul_le_mul_of_nonneg_left hRes (by linarith : (0:ℝ) ≤ g)
  have hcoef := mul_le_mul_of_nonneg_right (coef_bound P o) hS
  -- tail weights
  have hW : dN o * ∑ i : I, (band o u i)^2 ≤ ∑ i : I, P.weights o i * (band o u i)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ((h4 o).1 i) (sq_nonneg _))
  have hW' := mul_le_mul_of_nonneg_left hW hε0.le
  have hZ : ε * dN o * ‖z‖^2 ≤ ε * dM o * ‖z‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (dN_le_dM o) hε0.le) (sq_nonneg _)
  have hBF := RHBandNorm.band_far_norm o u hu
  rw [← hz] at hBF
  rw [hsplit] at hsum
  rw [hHg] at hH
  have hT : ε * dN o * ‖embed (tail o u)‖^2 = ε * (dN o * ∑ i : I, (band o u i)^2) + ε * dN o * ‖z‖^2 := by
    rw [← hBF]; ring
  rw [hT]
  nlinarith [hQ, hsum, hH, hLow, hF5, hF6, hcoef, hW', hZ]

/-! ## U-L7: norm decomposition of a component -/

lemma low_norm_sq (o : Bool) (u : ℝ → ℝ) :
    ‖embed (low o u)‖^2 = ∑ i : I, (alpha o u i)^2 := by
  have hm : ∀ i : I, MemLp (alpha o u i • basis (degree o i)) 2 volume :=
    fun i => (RHResidualMembership.basis_memLp _).const_smul _
  have he : embed (low o u) = ∑ i : I, alpha o u i • embed (basis (degree o i)) := by
    unfold low
    rw [RHBandNorm.embed_sum Finset.univ _ hm]
    exact Finset.sum_congr rfl (fun i _ =>
      RHBandNorm.embed_smul _ _ (RHResidualMembership.basis_memLp _))
  rw [he, ← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_sum]
  simp_rw [real_inner_smul_left, real_inner_smul_right, RHBandNorm.basis_inner,
    RHStepA2G2.degree_inj, Fin.val_inj]
  simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', sq]

lemma component_norm_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖embed (component o u)‖^2 = (∑ i : I, (alpha o u i)^2) + ‖embed (tail o u)‖^2 := by
  rw [RHStepA1G1.embed_norm_sq _ (RHG3RealEmbedding.component_memLp o u hu),
    RHStepA2G2.component_eq_low_add_tail, RHStepA2G2.integral_low_add_tail_sq o u hu,
    ← RHStepA1G1.embed_norm_sq _ (RHResidualMembership.low_memLp o u),
    ← RHStepA1G1.embed_norm_sq _ (RHResidualMembership.tail_memLp o u hu), low_norm_sq]

/-! ## U-L9: fixed-parity uniform bound (A1) -/

theorem component_lower_of_gates (P : Parameters)
    (h1 : G1 P) (h2 : G2 P) (h3 : G3 P) (h4 : G4 P)
    (h5 : RHCaps0494.G5c P RHT5Final0512.capsNew)
    (h6 : RHCaps0494.G6c P RHT5Final0512.capsNew)
    (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    c0 P o * ‖embed (component o u)‖^2 ≤ targetQ_real (component o u) := by
  have hq := component_quantitative P h1 h2 h3 h4 h5 h6 o u hu
  set S := ∑ i : I, (P.coordinates o u i)^2
  set A := ∑ i : I, (alpha o u i)^2
  set T := ‖embed (tail o u)‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT0 : 0 ≤ T := sq_nonneg _
  have hD := Dc_pos P o
  -- Σα² ≤ D S
  have hAS : A ≤ Dc P o * S := by
    have hα : P.B o *ᵥ P.coordinates o u = alpha o u := (h3 o u hu).1
    have h := mulVec_sq_le (P.B o) (P.coordinates o u)
    rw [hα] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS)
  have hc1 : c0 P o ≤ (9/1000) / (2 * Dc P o) := min_le_left _ _
  have hc2 : c0 P o ≤ eps P o * dN o := min_le_right _ _
  have hc0 := c0_pos P o
  have hA' : c0 P o * A ≤ (9/1000:ℝ)/2 * S := by
    calc c0 P o * A ≤ (9/1000) / (2 * Dc P o) * A := mul_le_mul_of_nonneg_right hc1 hA0
      _ ≤ (9/1000) / (2 * Dc P o) * (Dc P o * S) :=
          mul_le_mul_of_nonneg_left hAS (by positivity)
      _ = (9/1000:ℝ)/2 * S := by field_simp
  have hT' : c0 P o * T ≤ eps P o * dN o * T := mul_le_mul_of_nonneg_right hc2 hT0
  rw [component_norm_sq o u hu]
  nlinarith [hq, hA', hT']

/-- A1' for the concrete parameters. -/
noncomputable def cUniform : ℝ :=
  min (c0 RHConcreteParameters.concrete false) (c0 RHConcreteParameters.concrete true)

lemma cUniform_pos : 0 < cUniform :=
  lt_min (c0_pos _ _) (c0_pos _ _)

lemma cUniform_le (o : Bool) : cUniform ≤ c0 RHConcreteParameters.concrete o := by
  cases o
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem uniform_component_bound (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    cUniform * ‖embed (component o u)‖^2 ≤ targetQ_real (component o u) :=
  (mul_le_mul_of_nonneg_right (cUniform_le o) (sq_nonneg _)).trans
    (component_lower_of_gates RHConcreteParameters.concrete RHG1Adapter0484.g1 RHG2Final0489.g2
      RHSpectralInputs.g3_unconditional RHConcreteParameters.g4 RHT5Final0512.G5c_concrete
      RHFinalAll0524.G6c_concrete o u hu)

theorem uniform_component :
    ∃ c : ℝ, 0 < c ∧ ∀ (o : Bool) (u : ℝ → ℝ), Test u →
      c * ‖embed (component o u)‖^2 ≤ targetQ_real (component o u) :=
  ⟨cUniform, cUniform_pos, uniform_component_bound⟩

/-! ## U-L10, U-L11: real functions (A2) -/

lemma test_memLp (u : ℝ → ℝ) (hu : Test u) : MemLp u 2 volume :=
  hu.1.continuous.memLp_of_hasCompactSupport (RHAutocorrEnergy.compact_real hu.2)

lemma parity_integral_sq (u : ℝ → ℝ) (hu : Test u) :
    (∫ x, (u x)^2) = (∫ x, (component false u x)^2) + (∫ x, (component true u x)^2) := by
  have he := RHG3RealEmbedding.component_memLp false u hu
  have ho := RHG3RealEmbedding.component_memLp true u hu
  have hsum : u = fun x => component false u x + component true u x := by
    funext x; simp [component]; ring
  have hodd : (∫ x, component false u x * component true u x) = 0 := by
    have hneg : (fun x => component false u (-x) * component true u (-x)) =
        fun x => -(component false u x * component true u x) := by
      funext x; simp [component]; ring
    have h := MeasureTheory.integral_neg_eq_self
      (fun x => component false u x * component true u x) volume
    rw [hneg, integral_neg] at h
    linarith
  have hi1 : Integrable (fun x => (component false u x)^2) volume := he.integrable_sq
  have hi2 : Integrable (fun x => (component true u x)^2) volume := ho.integrable_sq
  have hi3 : Integrable (fun x => component false u x * component true u x) volume :=
    he.integrable_mul ho
  have hi4 : Integrable (fun x => 2 * (component false u x * component true u x)) volume :=
    hi3.const_mul 2
  have hi5 : Integrable (fun x => (component false u x)^2
      + 2 * (component false u x * component true u x)) volume := hi1.add hi4
  calc (∫ x, (u x)^2)
      = ∫ x, ((component false u x)^2 + 2 * (component false u x * component true u x)
          + (component true u x)^2) := by
        conv_lhs => rw [hsum]
        congr 1; funext x; ring
    _ = (∫ x, (component false u x)^2) + 2 * (∫ x, component false u x * component true u x)
          + (∫ x, (component true u x)^2) := by
        rw [integral_add hi5 hi2, integral_add hi1 hi4, integral_const_mul]
    _ = _ := by rw [hodd]; ring

theorem uniform_real_bound (u : ℝ → ℝ) (hu : Test u) :
    cUniform * (∫ x, (u x)^2) ≤ targetQ_real u := by
  have hs := targetQ_real_parity_split_of_test RHLog5Bridge.halfWidth_pos u
    (hu.1.of_le (by norm_num)) hu.2
  change targetQ_real u = targetQ_real (component false u) + targetQ_real (component true u) at hs
  have he := uniform_component_bound false u hu
  have ho := uniform_component_bound true u hu
  rw [RHStepA1G1.embed_norm_sq _ (RHG3RealEmbedding.component_memLp false u hu)] at he
  rw [RHStepA1G1.embed_norm_sq _ (RHG3RealEmbedding.component_memLp true u hu)] at ho
  rw [hs, parity_integral_sq u hu, mul_add]
  exact add_le_add he ho

theorem uniform_real :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ → ℝ, Test u → c * (∫ x, (u x)^2) ≤ targetQ_real u :=
  ⟨cUniform, cUniform_pos, uniform_real_bound⟩

/-! ## U-L12: final statement (A3) -/

theorem uniform_target_log5 :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → (∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) →
      Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
      c * (∫ x, ‖f x‖^2) ≤ (Zeta23.zetaZeroConfig.W f f).re := by
  refine ⟨cUniform, cUniform_pos, fun f hf hs => ⟨(RHComplexSpatialEndpoint.full_zero_log5 f hf hs).1, ?_⟩⟩
  have hre : Test (fun x => (f x).re) :=
    ⟨Complex.reCLM.contDiff.comp hf, RHComplexFrequency.re_support hs⟩
  have him : Test (fun x => (f x).im) :=
    ⟨Complex.imCLM.contDiff.comp hf, RHComplexFrequency.im_support hs⟩
  rw [RHTargetLog5.target_spatial_identity f hf hs, targetQ_split f hf hs,
    RHComplexSpatial.integral_norm_sq_parts hf.continuous (RHComplexFrequency.compact_of_support hs),
    mul_add]
  exact add_le_add (uniform_real_bound _ hre) (uniform_real_bound _ him)

end RHUniform0579

