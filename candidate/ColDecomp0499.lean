import Entry00Bounds0495
import ScaledEigen
import RealBasisBridge

/-! # 0499: exact decomposition of Weil column entries (well-conditioned form)

`∫ column L (basisPoly n) · basis k = (h0 + H_n)[n=k] + Rp + Tp + pole − prime`, using the exact
Legendre eigen-identity `∫ (P_n(x) − P_n(y))/|x−y| dy = 2 H_n P_n(x)` (0273/0276) for the `1/s` part
of the kernel `K(s) = 1/s + Rk(s)`. No numerics. -/

open MeasureTheory Set
open scoped BigOperators

namespace RHColDecomp0499
open RHConditionalLog5 RHLog5Bridge RHLowBlock0494 RHWeilColumnCandidate

local notation "Kk" => RH_GammaFinalFormula.K_kernel

/-- Smooth part of the kernel: `Rk s = K s − 1/s`. -/
noncomputable def Rk (s : ℝ) : ℝ := Kk s - 1 / s

/-- Real form of the Legendre eigen-identity for `basisPoly n` on `[-L, L]`. -/
theorem real_eigen (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-halfWidth) halfWidth) :
    (∫ y in (-halfWidth)..halfWidth, ((basisPoly n).eval x - (basisPoly n).eval y) / |x - y|) =
      2 * (harmonic n : ℝ) * (basisPoly n).eval x := by
  have h := RHTuckScaledEigen.integral_eigen halfWidth_pos n hx
  simp_rw [← RHRealBasisBridge.basisPoly_eval] at h
  have h2 : (∫ y in (-halfWidth)..halfWidth,
      ((((basisPoly n).eval x - (basisPoly n).eval y) / |x - y| : ℝ) : ℂ)) =
      2 * (harmonic n : ℂ) * (((basisPoly n).eval x : ℝ) : ℂ) := by
    rw [← h]; congr 1; funext y; push_cast; ring
  rw [intervalIntegral.integral_ofReal] at h2
  exact_mod_cast h2

lemma lip_real (p : Polynomial ℝ) : ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ x ∈ Icc (-halfWidth) halfWidth,
    ∀ y ∈ Icc (-halfWidth) halfWidth, |p.eval x - p.eval y| ≤ M1 * |x - y| := by
  obtain ⟨_M0, M1, _hM0, hM1, _hb, hl⟩ :=
    RHBoundedWindow.polynomial_bounds (p.map Complex.ofRealHom) halfWidth_pos.le
  refine ⟨M1, hM1, fun x hx y hy => ?_⟩
  have h := hl x hx y hy
  simp only [RHLowBlock0494.map_eval_ofReal] at h
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

lemma quot_bound (p : Polynomial ℝ) : ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ x ∈ Icc (-halfWidth) halfWidth,
    ∀ y ∈ Icc (-halfWidth) halfWidth, abs ((p.eval x - p.eval y) / |x - y|) ≤ M1 := by
  obtain ⟨M1, hM1, h⟩ := lip_real p
  refine ⟨M1, hM1, fun x hx y hy => ?_⟩
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy; simp [hM1]
  · have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    rw [abs_div, abs_abs, div_le_iff₀ hpos]
    exact h x hx y hy

lemma quot_integrableOn (p : Polynomial ℝ) {x : ℝ} (hx : x ∈ Icc (-halfWidth) halfWidth) :
    IntegrableOn (fun y => (p.eval x - p.eval y) / |x - y|) (Icc (-halfWidth) halfWidth) := by
  obtain ⟨M1, _, hb⟩ := quot_bound p
  have hmeas : AEStronglyMeasurable (fun y => (p.eval x - p.eval y) / |x - y|)
      (volume.restrict (Icc (-halfWidth) halfWidth)) :=
    ((measurable_const.sub p.continuous.measurable).div
      (measurable_const.sub measurable_id).abs).aestronglyMeasurable
  refine Measure.integrableOn_of_bounded (M := M1) (by simp [Real.volume_Icc]) ?_ ?_
  · exact ((measurable_const.sub p.continuous.measurable).div
      (measurable_const.sub measurable_id).abs).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (fun y hy => by
      rw [Real.norm_eq_abs]; exact hb x hx y hy))

/-- On the window, the kernel part of `colArch` splits into the `1/s` part (eigenvalue `2 H_n`)
and the smooth remainder `Rk`. -/
theorem kernel_split (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-halfWidth) halfWidth) :
    (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) =
      2 * (harmonic n : ℝ) * (basisPoly n).eval x +
      ∫ y in Icc (-halfWidth) halfWidth, Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y) := by
  have hK := RHColL2.kernel_eval_sub_integrableOn halfWidth halfWidth_pos.le (basisPoly n) x hx
  have hQ := quot_integrableOn (basisPoly n) hx
  have hpt : (fun y => Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) =
      fun y => Kk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y) -
        ((basisPoly n).eval x - (basisPoly n).eval y) / |x - y| := by
    funext y; unfold Rk; ring
  rw [hpt, integral_sub hK hQ, RHEntry00_0495.setI (fun y => ((basisPoly n).eval x - (basisPoly n).eval y) / |x - y|),
    real_eigen n hx]
  ring


/-! ### Main decomposition -/

noncomputable def colEntry (n k : ℕ) : ℝ := ∫ x, column halfWidth (basisPoly n) x * basis k x

lemma A0true_eq (o : Bool) (i j : I) : A0true o i j = colEntry (degree o j) (degree o i) := rfl
lemma Attrue_eq (o : Bool) (i j : I) : Attrue o i j = colEntry (degree o j) (degree o (32 + i)) := rfl

noncomputable def Rp (n k : ℕ) : ℝ := ∫ x in Icc (-halfWidth) halfWidth,
  (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) *
    (basisPoly k).eval x
noncomputable def Tp (n k : ℕ) : ℝ := ∫ x in Icc (-halfWidth) halfWidth,
  (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) *
    (basisPoly n).eval x * (basisPoly k).eval x
noncomputable def Cc (n : ℕ) : ℝ := ∫ y in Icc (-halfWidth) halfWidth, (basisPoly n).eval y * Real.cosh (y/2)
noncomputable def Ss (n : ℕ) : ℝ := ∫ y in Icc (-halfWidth) halfWidth, (basisPoly n).eval y * Real.sinh (y/2)
noncomputable def Pr (n k : ℕ) : ℝ := ∫ x in Icc (-halfWidth) halfWidth, primeTerm (basisPoly n) x * (basisPoly k).eval x

lemma basis_eq_zp (k : ℕ) : basis k = zp (basisPoly k) := rfl

lemma gram (n k : ℕ) : (∫ x in Icc (-halfWidth) halfWidth, (basisPoly n).eval x * (basisPoly k).eval x) =
    if n = k then 1 else 0 := by
  have h := RHBandNorm.basis_inner n k
  rw [RHBandNorm.inner_embed _ _ (RHResidualMembership.basis_memLp n) (RHResidualMembership.basis_memLp k),
    basis_eq_zp k, integral_mul_zp] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp only [basis_eq_zp, zp_of_mem _ hx]

lemma cont_intOn {g : ℝ → ℝ} (hg : Continuous g) : IntegrableOn g (Icc (-halfWidth) halfWidth) :=
  hg.integrableOn_Icc

lemma poly_memLp (q : Polynomial ℝ) : MemLp (fun x => q.eval x) 2 (volume.restrict (Icc (-halfWidth) halfWidth)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (-halfWidth) halfWidth)) := isFiniteMeasure_restrict.mpr (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (q.continuous.continuousOn (s := Icc (-halfWidth) halfWidth))
  exact MemLp.of_bound q.continuous.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hC))

lemma T_intOn (n k : ℕ) : IntegrableOn (fun x => (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth - x) +
    RH_Rebaseline.T_tail (halfWidth + x)) * (basisPoly n).eval x * (basisPoly k).eval x) (Icc (-halfWidth) halfWidth) := by
  have h := (RHColL2.tail_term_memLp halfWidth halfWidth_pos (basisPoly n)).integrable_mul (poly_memLp (basisPoly k))
  exact h

lemma K_intOn (n k : ℕ) : IntegrableOn (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
    Kk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x) (Icc (-halfWidth) halfWidth) :=
  (RHColL2.kernel_term_memLp_unconditional halfWidth halfWidth_pos.le (basisPoly n)).integrable_mul (poly_memLp (basisPoly k))

lemma R_intOn (n k : ℕ) : IntegrableOn (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
    Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x) (Icc (-halfWidth) halfWidth) := by
  have hH : IntegrableOn (fun x => (harmonic n : ℝ) * (basisPoly n).eval x * (basisPoly k).eval x)
      (Icc (-halfWidth) halfWidth) := cont_intOn (by fun_prop)
  refine ((K_intOn n k).sub hH).congr_fun (fun x hx => ?_) measurableSet_Icc
  simp only [Pi.sub_apply]
  rw [kernel_split n hx]
  ring

lemma prime_intOn (n k : ℕ) : IntegrableOn (fun x => primeTerm (basisPoly n) x * (basisPoly k).eval x)
    (Icc (-halfWidth) halfWidth) := by
  obtain ⟨C, _, hC⟩ := zp_bounded (basisPoly n)
  have hm : Measurable (primeTerm (basisPoly n)) := by
    unfold primeTerm
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
      (((zp_measurable _).comp (measurable_id.sub_const _)).add ((zp_measurable _).comp (measurable_id.add_const _))))
  have hb : ∀ x, |primeTerm (basisPoly n) x| ≤ ∑ i ∈ Finset.range 5,
      |(ArithmeticFunction.vonMangoldt i : ℝ) / Real.sqrt i| * (C + C) := by
    intro x
    unfold primeTerm
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (hC _) (hC _))) (abs_nonneg _)
  have hpB : IntegrableOn (primeTerm (basisPoly n)) (Icc (-halfWidth) halfWidth) :=
    Measure.integrableOn_of_bounded (by simp [Real.volume_Icc]) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hb x))
  obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((basisPoly k).continuous.continuousOn (s := Icc (-halfWidth) halfWidth))
  have h : IntegrableOn (fun x => (basisPoly k).eval x * primeTerm (basisPoly n) x) (Icc (-halfWidth) halfWidth) :=
    hpB.bdd_mul (c := Cq) (basisPoly k).continuous.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hCq))
  exact h.congr_fun (fun x _ => by ring) measurableSet_Icc

lemma lin7 {μ : Measure ℝ} {f1 f2 f3 f4 f5 f6 f7 : ℝ → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ)
    (h7 : Integrable f7 μ) :
    ∫ x, (f1 x + f2 x + f3 x + f4 x + f5 x - f6 x - f7 x) ∂μ =
      (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) + (∫ x, f4 x ∂μ) + (∫ x, f5 x ∂μ) -
        (∫ x, f6 x ∂μ) - (∫ x, f7 x ∂μ) := by
  have a2 : Integrable (fun x => f1 x + f2 x) μ := h1.add h2
  have a3 : Integrable (fun x => f1 x + f2 x + f3 x) μ := a2.add h3
  have a4 : Integrable (fun x => f1 x + f2 x + f3 x + f4 x) μ := a3.add h4
  have a5 : Integrable (fun x => f1 x + f2 x + f3 x + f4 x + f5 x) μ := a4.add h5
  have a6 : Integrable (fun x => f1 x + f2 x + f3 x + f4 x + f5 x - f6 x) μ := a5.sub h6
  rw [integral_sub a6 h7, integral_sub a5 h6, integral_add a4 h5, integral_add a3 h4,
    integral_add a2 h3, integral_add h1 h2]

/-- **Exact decomposition** of a Weil column entry in the well-conditioned (Legendre-diagonal) form. -/
theorem colEntry_decomp (n k : ℕ) :
    colEntry n k = (h0c + (harmonic n : ℝ)) * (if n = k then 1 else 0) + Rp n k + Tp n k +
      2 * Cc n * Cc k - 2 * Ss n * Ss k - Pr n k := by
  have hae : (fun x => column halfWidth (basisPoly n) x * basis k x) =ᵐ[volume]
      fun x => colFull (basisPoly n) x * zp (basisPoly k) x := by
    filter_upwards [Measure.ae_ne volume halfWidth, Measure.ae_ne volume (-halfWidth)] with x h1 h2
    rw [basis_eq_zp]
    by_cases hxI : x ∈ Icc (-halfWidth) halfWidth
    · have hlt : |x| < halfWidth :=
        abs_lt.mpr ⟨lt_of_le_of_ne hxI.1 (Ne.symm h2), lt_of_le_of_ne hxI.2 h1⟩
      rw [column_eq_colFull _ hlt]
    · rw [zp_of_not_mem _ hxI, mul_zero, mul_zero]
  unfold colEntry
  rw [integral_congr_ae hae, integral_mul_zp]
  set p := basisPoly n
  set q := basisPoly k
  have hpt : EqOn (fun x => colFull p x * q.eval x)
      (fun x => h0c * p.eval x * q.eval x + (harmonic n : ℝ) * (p.eval x * q.eval x) +
        (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, Rk |x - y| * (p.eval x - p.eval y)) * q.eval x +
        (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) * p.eval x * q.eval x +
        2 * Cc n * (q.eval x * Real.cosh (x/2)) - 2 * Ss n * (q.eval x * Real.sinh (x/2)) -
        primeTerm p x * q.eval x) (Icc (-halfWidth) halfWidth) := by
    intro x hx
    simp only [colFull, colArch]
    rw [kernel_split n hx]
    unfold Cc Ss
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hpt]
  have i1 : IntegrableOn (fun x => h0c * p.eval x * q.eval x) (Icc (-halfWidth) halfWidth) := cont_intOn (by fun_prop)
  have i2 : IntegrableOn (fun x => (harmonic n : ℝ) * (p.eval x * q.eval x)) (Icc (-halfWidth) halfWidth) :=
    cont_intOn (by fun_prop)
  have i3 := R_intOn n k
  have i4 := T_intOn n k
  have i5 : IntegrableOn (fun x => 2 * Cc n * (q.eval x * Real.cosh (x/2))) (Icc (-halfWidth) halfWidth) :=
    cont_intOn (by fun_prop)
  have i6 : IntegrableOn (fun x => 2 * Ss n * (q.eval x * Real.sinh (x/2))) (Icc (-halfWidth) halfWidth) :=
    cont_intOn (by fun_prop)
  have i7 := prime_intOn n k
  rw [lin7 i1 i2 i3 i4 i5 i6 i7]
  have e1 : (∫ x in Icc (-halfWidth) halfWidth, h0c * p.eval x * q.eval x) = h0c * (if n = k then 1 else 0) := by
    rw [show (fun x => h0c * p.eval x * q.eval x) = fun x => h0c * (p.eval x * q.eval x) by funext x; ring,
      integral_const_mul, gram]
  have e2 : (∫ x in Icc (-halfWidth) halfWidth, (harmonic n : ℝ) * (p.eval x * q.eval x)) =
      (harmonic n : ℝ) * (if n = k then 1 else 0) := by rw [integral_const_mul, gram]
  have e5 : (∫ x in Icc (-halfWidth) halfWidth, 2 * Cc n * (q.eval x * Real.cosh (x/2))) = 2 * Cc n * Cc k := by
    rw [integral_const_mul]; rfl
  have e6 : (∫ x in Icc (-halfWidth) halfWidth, 2 * Ss n * (q.eval x * Real.sinh (x/2))) = 2 * Ss n * Ss k := by
    rw [integral_const_mul]; rfl
  rw [e1, e2, e5, e6]
  unfold Rp Tp Pr
  ring

end RHColDecomp0499

