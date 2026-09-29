import TailL2
import ConditionalLog5
import WeilColumnCandidate
import ResidualMembership
import Final
import WindowEnergy
import AutocorrEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open RHTailL2 RH_Rebaseline RHConditionalLog5 RHWeilColumnCandidate RHBoundedWindow RHFormDomain RHAutocorrEnergy

namespace RHColL2

/-- Any real polynomial zero-extended from Icc (-L) L belongs to Lp(ℝ, volume). -/
lemma zeroPoly_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    MemLp (zeroPoly L p) 2 volume := by
  let P_complex : Polynomial ℂ := p.map Complex.ofRealHom
  have hp : MemLp (fun x : ℝ => P_complex.eval (x : ℂ)) 2 (volume.restrict (Icc (-L) L)) :=
    polynomial_memLp hL P_complex
  have hc : MemLp (fun x : ℝ => (Icc (-L) L).indicator (fun y => P_complex.eval (y : ℂ)) x) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr hp
  have heq : zeroPoly L p = fun x => ((Icc (-L) L).indicator (fun y => P_complex.eval (y : ℂ)) x).re := by
    ext x
    unfold zeroPoly indicator
    split_ifs with hx
    · dsimp only
      have heval : P_complex.eval (x : ℂ) = Complex.ofRealHom (p.eval x) := by
        dsimp [P_complex]
        rw [Polynomial.eval_map]
        exact Polynomial.eval₂_at_apply Complex.ofRealHom x
      rw [heval]
      rfl
    · rfl
  rw [heq]
  exact Complex.reCLM.comp_memLp' hc

/-- The indicator over open interval (-L, L) on real line is equivalent to MemLp on restrict Icc (-L) L. -/
lemma memLp_indicator_Ioo_iff (L : ℝ) (f : ℝ → ℝ) :
    MemLp (fun x => if |x| < L then f x else 0) 2 volume ↔
    MemLp f 2 (volume.restrict (Icc (-L) L)) := by
  have heq : (fun x => if |x| < L then f x else 0) = (Ioo (-L) L).indicator f := by
    ext x
    unfold indicator
    simp [abs_lt]
  rw [heq]
  rw [memLp_indicator_iff_restrict measurableSet_Ioo]
  rw [restrict_Ioo_eq_restrict_Icc]

/-- Polynomial evaluation on Icc (-L) L is MemLp. -/
lemma poly_eval_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    MemLp (fun x => p.eval x) 2 (volume.restrict (Icc (-L) L)) := by
  let P_complex : Polynomial ℂ := p.map Complex.ofRealHom
  have hp : MemLp (fun x : ℝ => P_complex.eval (x : ℂ)) 2 (volume.restrict (Icc (-L) L)) :=
    polynomial_memLp hL P_complex
  have heq : (fun x => p.eval x) = fun x : ℝ => (P_complex.eval (x : ℂ)).re := by
    ext x
    have heval : P_complex.eval (x : ℂ) = Complex.ofRealHom (p.eval x) := by
      dsimp [P_complex]
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply Complex.ofRealHom x
    rw [heval]
    rfl
  rw [heq]
  exact Complex.reCLM.comp_memLp' hp

lemma continuous_cosh_half : Continuous (fun x : ℝ => Real.cosh (x / 2)) :=
  Real.continuous_cosh.comp (continuous_id.div_const 2)

lemma continuous_sinh_half : Continuous (fun x : ℝ => Real.sinh (x / 2)) :=
  Real.continuous_sinh.comp (continuous_id.div_const 2)

/-- cosh(x/2) on Icc (-L) L is MemLp. -/
lemma cosh_half_memLp (L : ℝ) :
    MemLp (fun x => Real.cosh (x / 2)) 2 (volume.restrict (Icc (-L) L)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_cosh_half.continuousOn (s := Icc (-L) L))
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ x ∈ Icc (-L) L, ‖Real.cosh (x / 2)‖ ≤ M := fun x hx =>
    (hC x hx).trans (le_max_left _ _)
  have : IsFiniteMeasure (volume.restrict (Icc (-L) L)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact MemLp.of_bound continuous_cosh_half.aestronglyMeasurable M
    (ae_restrict_of_forall_mem measurableSet_Icc hMb)

/-- sinh(x/2) on Icc (-L) L is MemLp. -/
lemma sinh_half_memLp (L : ℝ) :
    MemLp (fun x => Real.sinh (x / 2)) 2 (volume.restrict (Icc (-L) L)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_sinh_half.continuousOn (s := Icc (-L) L))
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ x ∈ Icc (-L) L, ‖Real.sinh (x / 2)‖ ≤ M := fun x hx =>
    (hC x hx).trans (le_max_left _ _)
  have : IsFiniteMeasure (volume.restrict (Icc (-L) L)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact MemLp.of_bound continuous_sinh_half.aestronglyMeasurable M
    (ae_restrict_of_forall_mem measurableSet_Icc hMb)

/-- A polynomial is bounded on compact Icc (-L) L. -/
lemma poly_exists_bound (L : ℝ) (p : Polynomial ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-L) L, |p.eval x| ≤ M := by
  have hcont : Continuous (fun x : ℝ => p.eval x) := p.continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (-L) L))
  refine ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-- Multiplying an L^2 function on Icc (-L) L by a polynomial preserves L^2. -/
lemma memLp_two_mul_poly (L : ℝ) (p : Polynomial ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Icc (-L) L))) :
    MemLp (fun x => f x * p.eval x) 2 (volume.restrict (Icc (-L) L)) := by
  obtain ⟨M, _hM, hMb⟩ := poly_exists_bound L p
  have h_meas : AEStronglyMeasurable (fun x => f x * p.eval x) (volume.restrict (Icc (-L) L)) :=
    hf.aestronglyMeasurable.mul p.continuous.aestronglyMeasurable
  refine hf.of_le_mul (c := M) h_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hMb x hx) (abs_nonneg _)

/-- The logarithmic tail term with polynomial factor belongs to L^2 on Icc (-L) L. -/
lemma tail_term_memLp (L : ℝ) (hL : 0 < L) (p : Polynomial ℝ) :
    MemLp (fun x => (1/2:ℝ) * (T_tail (L-x) + T_tail (L+x)) * p.eval x) 2
      (volume.restrict (Icc (-L) L)) := by
  have hr := right_tail_memLp_two L hL
  have hl := left_tail_memLp_two L hL
  have h_add := hr.add hl
  have h_mul := memLp_two_mul_poly L p (fun x => T_tail (L-x) + T_tail (L+x)) h_add
  have heq : (fun x => (1/2:ℝ) * (T_tail (L-x) + T_tail (L+x)) * p.eval x) =
      (1/2:ℝ) • (fun x => (T_tail (L-x) + T_tail (L+x)) * p.eval x) := by
    ext x
    dsimp
    ring
  rw [heq]
  exact h_mul.const_smul (1/2:ℝ)

/-- Translation invariance of L^2 under right addition on ℝ. -/
lemma memLp_comp_add_right (f : ℝ → ℝ) (c : ℝ)
    (hf : MemLp f 2 volume) :
    MemLp (fun x => f (x + c)) 2 volume := by
  have hA : MeasurableEmbedding (fun x : ℝ => x + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map (fun x => x + c) volume = volume :=
    map_add_right_eq_self volume c
  have h : MemLp (f ∘ (fun x => x + c)) 2 volume := by
    rw [← hmap] at hf
    exact hA.memLp_map_measure_iff.mp hf
  exact h

/-- Translation invariance of L^2 under right subtraction on ℝ. -/
lemma memLp_comp_sub_right (f : ℝ → ℝ) (c : ℝ)
    (hf : MemLp f 2 volume) :
    MemLp (fun x => f (x - c)) 2 volume := by
  have heq : (fun x => f (x - c)) = fun x => f (x + (-c)) := by
    ext x
    rw [sub_eq_add_neg]
  rw [heq]
  exact memLp_comp_add_right f (-c) hf

/-- Shifted zero-extended polynomial belongs to L^2(ℝ, volume). -/
lemma zeroPoly_shift_sub_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) (c : ℝ) :
    MemLp (fun x => zeroPoly L p (x - c)) 2 volume :=
  memLp_comp_sub_right (zeroPoly L p) c (zeroPoly_memLp L hL p)

lemma zeroPoly_shift_add_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) (c : ℝ) :
    MemLp (fun x => zeroPoly L p (x + c)) 2 volume :=
  memLp_comp_add_right (zeroPoly L p) c (zeroPoly_memLp L hL p)

/-- Term 1 is MemLp on Icc. -/
lemma term1_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    MemLp (fun x => ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * p.eval x) 2
      (volume.restrict (Icc (-L) L)) :=
  (poly_eval_memLp L hL p).const_mul _

/-- Term 4 is MemLp on Icc. -/
lemma term4_memLp (L : ℝ) (p : Polynomial ℝ) :
    MemLp (fun x => 2 * (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) * Real.cosh (x/2)) 2
      (volume.restrict (Icc (-L) L)) :=
  (cosh_half_memLp L).const_mul _

/-- Term 5 is MemLp on Icc. -/
lemma term5_memLp (L : ℝ) (p : Polynomial ℝ) :
    MemLp (fun x => 2 * (∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) * Real.sinh (x/2)) 2
      (volume.restrict (Icc (-L) L)) :=
  (sinh_half_memLp L).const_mul _

/-- Shifted zeroPoly is MemLp on Icc. -/
lemma zeroPoly_shift_sub_restrict (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) (c : ℝ) :
    MemLp (fun x => zeroPoly L p (x - c)) 2 (volume.restrict (Icc (-L) L)) :=
  (zeroPoly_shift_sub_memLp L hL p c).mono_measure Measure.restrict_le_self

lemma zeroPoly_shift_add_restrict (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) (c : ℝ) :
    MemLp (fun x => zeroPoly L p (x + c)) 2 (volume.restrict (Icc (-L) L)) :=
  (zeroPoly_shift_add_memLp L hL p c).mono_measure Measure.restrict_le_self

/-- Single prime term is MemLp on Icc. -/
lemma prime_single_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) (n : ℕ) :
    MemLp (fun x => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (zeroPoly L p (x - Real.log n) + zeroPoly L p (x + Real.log n))) 2
      (volume.restrict (Icc (-L) L)) := by
  have hsub := zeroPoly_shift_sub_restrict L hL p (Real.log n)
  have hadd := zeroPoly_shift_add_restrict L hL p (Real.log n)
  exact (hsub.add hadd).const_mul _

/-- Term 6 (prime sum) is MemLp on Icc. -/
lemma term6_memLp (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    MemLp (fun x => ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (zeroPoly L p (x - Real.log n) + zeroPoly L p (x + Real.log n))) 2
      (volume.restrict (Icc (-L) L)) :=
  memLp_finsetSum (Finset.range 5) (fun n _ => prime_single_memLp L hL p n)

/-- The interior expression of the Weil column before indicator truncation. -/
noncomputable def column_inner (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * p.eval x +
  (1/2:ℝ) * (∫ y in Icc (-L) L,
    RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) +
  (1/2:ℝ) * (RH_Rebaseline.T_tail (L-x) + RH_Rebaseline.T_tail (L+x)) * p.eval x +
  2 * (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) * Real.cosh (x/2) -
  2 * (∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) * Real.sinh (x/2) -
  ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (zeroPoly L p (x-Real.log n) + zeroPoly L p (x+Real.log n))

lemma column_eq_indicator (L : ℝ) (p : Polynomial ℝ) :
    column L p = fun x => if |x| < L then column_inner L p x else 0 := rfl

theorem column_inner_memLp (L : ℝ) (hL : 0 < L) (p : Polynomial ℝ)
    (h_kernel : MemLp (fun x => (1/2:ℝ) * (∫ y in Icc (-L) L,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y))) 2 (volume.restrict (Icc (-L) L))) :
    MemLp (column_inner L p) 2 (volume.restrict (Icc (-L) L)) := by
  have h1 := term1_memLp L hL.le p
  have h2 := h_kernel
  have h3 := tail_term_memLp L hL p
  have h4 := term4_memLp L p
  have h5 := term5_memLp L p
  have h6 := term6_memLp L hL.le p
  have h12 := h1.add h2
  have h123 := h12.add h3
  have h1234 := h123.add h4
  have h12345 := h1234.sub h5
  have h_all := h12345.sub h6
  exact h_all

theorem column_memLp_of_kernel (L : ℝ) (hL : 0 < L) (p : Polynomial ℝ)
    (h_kernel : MemLp (fun x => (1/2:ℝ) * (∫ y in Icc (-L) L,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y))) 2 (volume.restrict (Icc (-L) L))) :
    MemLp (column L p) 2 volume := by
  rw [column_eq_indicator]
  rw [memLp_indicator_Ioo_iff]
  exact column_inner_memLp L hL p h_kernel

lemma measurable_K_kernel : Measurable RH_GammaFinalFormula.K_kernel := by
  unfold RH_GammaFinalFormula.K_kernel RH_GammaSqrtBound.K_kernel
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).measurable.div
    Real.continuous_sinh.measurable

lemma measurable_kernel_prod (p : Polynomial ℝ) :
    Measurable (fun z : ℝ × ℝ => RH_GammaFinalFormula.K_kernel |z.1 - z.2| * (p.eval z.1 - p.eval z.2)) := by
  have h1 : Measurable (fun z : ℝ × ℝ => |z.1 - z.2|) :=
    (continuous_fst.sub continuous_snd).abs.measurable
  have hK : Measurable (fun z : ℝ × ℝ => RH_GammaFinalFormula.K_kernel |z.1 - z.2|) :=
    measurable_K_kernel.comp h1
  have hp : Continuous (fun z : ℝ × ℝ => p.eval z.1 - p.eval z.2) :=
    (p.continuous.comp continuous_fst).sub (p.continuous.comp continuous_snd)
  exact hK.mul hp.measurable

lemma stronglyMeasurable_kernel_prod (p : Polynomial ℝ) :
    StronglyMeasurable (fun z : ℝ × ℝ => RH_GammaFinalFormula.K_kernel |z.1 - z.2| * (p.eval z.1 - p.eval z.2)) :=
  (measurable_kernel_prod p).stronglyMeasurable

lemma aestronglyMeasurable_integral (L : ℝ) (p : Polynomial ℝ) :
    AEStronglyMeasurable (fun x => ∫ y in Icc (-L) L,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) (volume.restrict (Icc (-L) L)) := by
  let μ := volume.restrict (Icc (-L) L)
  have hs : StronglyMeasurable (fun z : ℝ × ℝ =>
      RH_GammaFinalFormula.K_kernel |z.1 - z.2| * (p.eval z.1 - p.eval z.2)) :=
    stronglyMeasurable_kernel_prod p
  have hi : StronglyMeasurable (fun x => ∫ y,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y) ∂μ) :=
    hs.integral_prod_right'
  exact hi.aestronglyMeasurable

lemma kernel_term_memLp (L : ℝ) (_hL : 0 ≤ L) (p : Polynomial ℝ)
    (C : ℝ)
    (hC : ∀ x ∈ Icc (-L) L, ‖∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤ C) :
    MemLp (fun x => ∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) 2
      (volume.restrict (Icc (-L) L)) := by
  have h_meas := aestronglyMeasurable_integral L p
  have _h_fin : IsFiniteMeasure (volume.restrict (Icc (-L) L)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  let M := max C 0
  have _hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ x ∈ Icc (-L) L, ‖∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤ M :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  exact MemLp.of_bound h_meas M (ae_restrict_of_forall_mem measurableSet_Icc hMb)

lemma kernel_eval_sub_le (L : ℝ) (_hL : 0 ≤ L) (p : Polynomial ℝ)
    (M1 : ℝ) (hl : LipschitzBoundOn L (fun x => (p.map Complex.ofRealHom).eval (x:ℂ)) M1)
    (x y : ℝ) (hx : x ∈ Icc (-L) L) (hy : y ∈ Icc (-L) L) :
    ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤
      M1 * (min |x-y| (2*L) * RH_GammaFinalFormula.K_kernel |x-y|) := by
  have hk : 0 ≤ RH_GammaFinalFormula.K_kernel |x-y| := RHAutocorrEnergy.kernel_abs_nonneg (x - y)
  have heval_x : (p.map Complex.ofRealHom).eval (x:ℂ) = Complex.ofRealHom (p.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply Complex.ofRealHom x
  have heval_y : (p.map Complex.ofRealHom).eval (y:ℂ) = Complex.ofRealHom (p.eval y) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply Complex.ofRealHom y
  have hlip := hl x hx y hy
  dsimp only at hlip
  rw [heval_x, heval_y] at hlip
  have hdiff : Complex.ofRealHom (p.eval x) - Complex.ofRealHom (p.eval y) =
      ((p.eval x - p.eval y : ℝ) : ℂ) := by
    simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_sub]
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs] at hlip
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  have hxy2L : |x - y| ≤ 2 * L := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hmin : |x - y| = min |x - y| (2 * L) := (min_eq_left hxy2L).symm
  rw [hmin] at hlip
  calc
    RH_GammaFinalFormula.K_kernel |x-y| * |p.eval x - p.eval y|
      ≤ RH_GammaFinalFormula.K_kernel |x-y| * (M1 * min |x-y| (2*L)) :=
        mul_le_mul_of_nonneg_left hlip hk
    _ = M1 * (min |x-y| (2*L) * RH_GammaFinalFormula.K_kernel |x-y|) := by ring

lemma kernel_eval_sub_integrableOn (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ)
    (x : ℝ) (hx : x ∈ Icc (-L) L) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) (Icc (-L) L) volume := by
  let P_complex : Polynomial ℂ := p.map Complex.ofRealHom
  obtain ⟨_M0, M1, _hM0, _hM1, _hb, hl⟩ := polynomial_bounds P_complex hL
  let F : ℝ → ℝ := fun s => min |s| (2*L) * RH_GammaFinalFormula.K_kernel |s|
  have hF_int : Integrable F volume := full_moment_integrable (by linarith : 0 ≤ 2*L)
  have h_meas : AEStronglyMeasurable (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y))
      (volume.restrict (Icc (-L) L)) :=
    (stronglyMeasurable_kernel_prod p).comp_measurable (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
  have h_le_ptwise : ∀ y ∈ Icc (-L) L,
      ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤ M1 * F (x - y) := by
    intro y hy
    exact kernel_eval_sub_le L hL p M1 hl x y hx hy
  have hG_int : Integrable (fun y => M1 * F (x - y)) volume :=
    (hF_int.comp_sub_left x).const_mul M1
  have hG_intOn : IntegrableOn (fun y => M1 * F (x - y)) (Icc (-L) L) volume :=
    hG_int.integrableOn
  apply Integrable.mono' hG_intOn h_meas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact h_le_ptwise y hy

lemma kernel_integral_bound (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc (-L) L,
      ‖∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤ C := by
  let P_complex : Polynomial ℂ := p.map Complex.ofRealHom
  obtain ⟨_M0, M1, _hM0, hM1, _hb, hl⟩ := polynomial_bounds P_complex hL
  let F : ℝ → ℝ := fun s => min |s| (2*L) * RH_GammaFinalFormula.K_kernel |s|
  have hF_int : Integrable F volume := full_moment_integrable (by linarith : 0 ≤ 2*L)
  have hF_nonneg : ∀ s, 0 ≤ F s := full_moment_nonneg (by linarith : 0 ≤ 2*L)
  refine ⟨M1 * (∫ s, F s), ?_⟩
  intro x hx
  have h_meas : AEStronglyMeasurable (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y))
      (volume.restrict (Icc (-L) L)) :=
    (stronglyMeasurable_kernel_prod p).comp_measurable (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
  have h_le_ptwise : ∀ y ∈ Icc (-L) L,
      ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤ M1 * F (x - y) := by
    intro y hy
    exact kernel_eval_sub_le L hL p M1 hl x y hx hy
  have hG_int : Integrable (fun y => M1 * F (x - y)) volume :=
    (hF_int.comp_sub_left x).const_mul M1
  have hG_intOn : IntegrableOn (fun y => M1 * F (x - y)) (Icc (-L) L) volume :=
    hG_int.integrableOn
  have hf_intOn : IntegrableOn (fun y => ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖) (Icc (-L) L) volume := by
    apply Integrable.mono' hG_intOn h_meas.norm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [norm_norm]
    exact h_le_ptwise y hy
  have h_norm_le : ‖∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ ≤
      ∫ y in Icc (-L) L, ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict (Icc (-L) L)) _
  have h_int_le : (∫ y in Icc (-L) L, ‖RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)‖) ≤
      ∫ y in Icc (-L) L, M1 * F (x - y) :=
    setIntegral_mono_on hf_intOn hG_intOn measurableSet_Icc h_le_ptwise
  have h_restrict_le : (∫ y in Icc (-L) L, M1 * F (x - y)) ≤ ∫ y, M1 * F (x - y) := by
    have h_nonneg_pt : 0 ≤ᵐ[volume] (fun y => M1 * F (x - y)) :=
      Eventually.of_forall (fun y => mul_nonneg hM1 (hF_nonneg (x - y)))
    exact setIntegral_le_integral hG_int h_nonneg_pt
  have h_sub : (∫ y, M1 * F (x - y)) = M1 * ∫ s, F s := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self F volume x
  linarith

theorem kernel_term_memLp_unconditional (L : ℝ) (hL : 0 ≤ L) (p : Polynomial ℝ) :
    MemLp (fun x => (1/2:ℝ) * (∫ y in Icc (-L) L,
      RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y))) 2
      (volume.restrict (Icc (-L) L)) := by
  obtain ⟨C, hC⟩ := kernel_integral_bound L hL p
  exact (kernel_term_memLp L hL p C hC).const_mul (1/2:ℝ)

/-- Unconditional L^2 membership for any Weil column candidate on any interval L > 0. -/
theorem column_memLp_unconditional (L : ℝ) (hL : 0 < L) (p : Polynomial ℝ) :
    MemLp (column L p) 2 volume :=
  column_memLp_of_kernel L hL p (kernel_term_memLp_unconditional L hL.le p)

end RHColL2
