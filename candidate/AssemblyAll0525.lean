import ColParity0520
import GammaThm0516
import Interface0516
import Interface0524
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import PolyExp0522
import ResidualApprox0494
import SxScale0516

/- Source: Error0525.lean -/

open MeasureTheory Finset
open scoped BigOperators

namespace RHError0525

lemma young_sub (a b η : ℝ) (hη : 0 < η) :
    (a-b)^2 ≤ (1+1/η)*a^2 + (1+η)*b^2 := by
  have h := sq_nonneg (a+η*b)
  have he : η*((1+1/η)*a^2+(1+η)*b^2-(a-b)^2) = (a+η*b)^2 := by
    field_simp
    <;> ring
  nlinarith

theorem integral_young_sub (a b : ℝ → ℝ)
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (η : ℝ) (hη : 0 < η) :
    (∫ x, (a x-b x)^2) ≤
      (1+1/η)*(∫ x, a x^2)+(1+η)*(∫ x,b x^2) := by
  have hab : Integrable (fun x => (a x-b x)^2) volume := (ha.sub hb).integrable_sq
  have h1 := ha.integrable_sq.const_mul (1+1/η)
  have h2 := hb.integrable_sq.const_mul (1+η)
  have h := integral_mono_ae hab (h1.add h2)
    (Filter.Eventually.of_forall (fun x => young_sub (a x) (b x) η hη))
  simp only [Pi.add_apply] at h
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul] at h
  exact h

lemma weighted_error {ι : Type*} [Fintype ι] (b z : ι → ℝ) (δ : ℝ)
    (hz : ∀ i, |z i| ≤ δ) :
    |∑ i, b i*z i| ≤ δ*∑ i, |b i| := by
  calc
    |∑ i, b i*z i| ≤ ∑ i, |b i*z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |b i| * δ := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hz i) (abs_nonneg _))
    _ = δ*∑ i, |b i| := by rw [← Finset.sum_mul]; ring

end RHError0525

/- Source: Gram0525.lean -/
open MeasureTheory Finset
open scoped BigOperators
namespace RHGram0525

lemma sum_memLp {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 volume) (b : ι → ℝ) :
    MemLp (fun x => ∑ i, b i * f i x) 2 volume := by
  convert memLp_finsetSum' Finset.univ (fun i _ => (hf i).const_mul (b i)) using 1
  funext x
  simp only [Finset.sum_apply]

lemma gram_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 volume) (b : ι → ℝ) :
    (∫ x, (∑ i, b i*f i x)^2) =
      ∑ i, ∑ k, b i*b k*(∫ x, f i x*f k x) := by
  have he : (fun x => (∑ i, b i*f i x)^2) =
      fun x => ∑ i, ∑ k, b i*b k*(f i x*f k x) := by
    funext x
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro k _
      exact ((hf i).integrable_mul (hf k)).const_mul _
  · intro i _
    exact integrable_finset_sum _ (fun k _ => ((hf i).integrable_mul (hf k)).const_mul _)

lemma sum_inner {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 volume) (b : ι → ℝ)
    (e : ℝ → ℝ) (he : MemLp e 2 volume) :
    (∫ x, (∑ i, b i*f i x)*e x) = ∑ i, b i*(∫ x, f i x*e x) := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ
    (f := fun i x => b i * (f i x * e x))
    (fun i _ => by simpa only [Pi.mul_apply] using ((hf i).integrable_mul he).const_mul (b i))]
  simp only [integral_const_mul]
end RHGram0525

/- Source: Uniform0525.lean -/
open MeasureTheory Set
namespace RHUniform0525
lemma bounded_sq (a : ℝ → ℝ) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hz : ∀ x, x ∉ Icc (-L) L → a x = 0)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc (-L) L → |a x| ≤ C) :
    (∫ x, a x^2) ≤ 2*L*C^2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [hz x hx]; norm_num : ∀ x, x ∉ Icc (-L) L → a x^2 = 0)]
  have h := norm_setIntegral_le_of_norm_le_const_ae'
    (f := fun x => a x^2) (C := C^2) (isCompact_Icc.measure_lt_top (μ := volume))
    (by
      filter_upwards [hb] with x hx
      intro hxi
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a x)) (hx hxi) 2)
  rw [Real.volume_real_Icc_of_le (by linarith : -L ≤ L)] at h
  have hle := le_abs_self (∫ x in Icc (-L) L, a x^2)
  rw [Real.norm_eq_abs] at h
  nlinarith
end RHUniform0525

/- Source: SxLp0525.lean -/

open MeasureTheory Set
namespace RHSxLp0525
open RHLeg0503 RHSingDef0516 RHInterface0516 RHLog5Bridge

lemma pm_measurable (n : ℕ) (s : ℝ) : Measurable (pm n s) := by
  unfold pm
  exact Measurable.ite measurableSet_Ioi
    ((continuous_p n).comp (continuous_id.sub continuous_const)).measurable measurable_const

lemma pp_measurable (n : ℕ) (s : ℝ) : Measurable (pp n s) := by
  unfold pp
  exact Measurable.ite measurableSet_Iic
    ((continuous_p n).comp (continuous_id.add continuous_const)).measurable measurable_const

lemma pr_measurable (n : ℕ) : Measurable (pr n) := by
  unfold pr
  have h2 := (pm_measurable n (σ 2)).add (pp_measurable n (σ 2))
  have h3 := (pm_measurable n (σ 3)).add (pp_measurable n (σ 3))
  have h4 := (pm_measurable n (σ 4)).add (pp_measurable n (σ 4))
  exact ((measurable_const.mul h2).add (measurable_const.mul h3)).add
    (measurable_const.mul h4)

lemma phi_measurable (n : ℕ) : Measurable (phi n) := by
  have hl : Measurable lg := by unfold lg; fun_prop
  exact ((measurable_const.mul hl).mul (continuous_p n).measurable).add (pr_measurable n)

lemma Sx_measurable (n : ℕ) : Measurable (Sx n) := by
  unfold Sx
  exact Measurable.ite (measurableSet_lt measurable_id.abs measurable_const)
    (measurable_const.mul ((phi_measurable n).comp (measurable_id.div_const halfWidth)))
    measurable_const

lemma phi_mul_ii (i k : ℕ) :
    IntervalIntegrable (fun u => phi i u * phi k u) volume (-1) 1 := by
  have h := (((RHGammaThm0516.AA_ii i k).add (RHGammaThm0516.Apr_ii i k)).add
    (RHGammaThm0516.prA_ii i k)).add (RHGammaThm0516.prpr_ii i k)
  refine h.congr (fun u _ => ?_)
  simp only [RHGammaThm0516.phi_eq]
  ring

lemma phi_sq_ii (n : ℕ) :
    IntervalIntegrable (fun u => phi n u ^ 2) volume (-1) 1 := by
  simpa only [pow_two] using phi_mul_ii n n

lemma Sx_sq_integrable (n : ℕ) : Integrable (fun x => Sx n x ^ 2) volume := by
  have hL := halfWidth_pos
  have hi : IntegrableOn (fun u => phi n u ^ 2) (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp (phi_sq_ii n)
  have hz : Integrable ((Ioo (-1:ℝ) 1).indicator (fun u => phi n u ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hi
  have he : (fun u => Sx n (halfWidth*u)^2) = fun u =>
      RHRpExact0506.cc n ^ 2 * (Ioo (-1:ℝ) 1).indicator (fun u => phi n u ^ 2) u := by
    funext u
    by_cases hu : u ∈ Ioo (-1:ℝ) 1
    · rw [indicator_of_mem hu, RHSxScale0516.Sx_scale n hu.1 hu.2, mul_pow]
    · rw [indicator_of_notMem hu, mul_zero]
      have hx : ¬ |halfWidth*u| < halfWidth := by
        intro hh
        have hh' : halfWidth * |u| < halfWidth * 1 := by
          simpa only [abs_mul, abs_of_pos hL, mul_one] using hh
        have huabs : |u| < 1 := by nlinarith
        exact hu (abs_lt.mp huabs)
      simp only [Sx, if_neg hx, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  apply (integrable_comp_mul_left_iff (fun x => Sx n x ^ 2) hL.ne').mp
  rw [he]
  exact hz.const_mul _

/-- The fixed singular column part belongs to real L² on the full line. -/
theorem Sx_memLp (n : ℕ) : MemLp (RHInterface0516.Sx n) 2 volume :=
  (memLp_two_iff_integrable_sq (Sx_measurable n).aestronglyMeasurable).mpr
    (Sx_sq_integrable n)

lemma Sx_mul_integrable (i k : ℕ) : Integrable (fun x => Sx i x * Sx k x) volume :=
  (Sx_memLp i).integrable_mul (Sx_memLp k)

end RHSxLp0525

/- Source: Projection0525.lean -/

/-! Finite L² projection onto the 64 fixed directions of one parity.
No support, parity, smoothness, or measurability assumption beyond MemLp is added to S.
This module does not import Interface0524 or PolyExp0522. -/

open MeasureTheory
open scoped BigOperators
namespace RHProjection0525
open RHConditionalLog5 RHResidualMembership

noncomputable def sco (o : Bool) (S : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ x, S x * basis (degree o m) x

noncomputable def proj (o : Bool) (S : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 64, sco o S m * basis (degree o m) x

lemma proj_memLp (o : Bool) (S : ℝ → ℝ) : MemLp (proj o S) 2 volume := by
  have h := memLp_finsetSum' (Finset.range 64)
    (fun m _ => (basis_memLp (degree o m)).const_mul (sco o S m))
  convert h using 1
  funext x
  simp [proj, Finset.sum_apply]

lemma residual_memLp (o : Bool) (S : ℝ → ℝ) (hS : MemLp S 2 volume) :
    MemLp (fun x => S x - proj o S x) 2 volume :=
  hS.sub (proj_memLp o S)

lemma sco_inner (o : Bool) (S : ℝ → ℝ) (hS : MemLp S 2 volume) (m : ℕ) :
    inner ℝ (embed (basis (degree o m))) (embed S) = sco o S m := by
  rw [RHBandNorm.inner_embed _ _ (basis_memLp _) hS]
  unfold sco
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

lemma embed_proj (o : Bool) (S : ℝ → ℝ) :
    embed (proj o S) = ∑ m ∈ Finset.range 64, sco o S m • embed (basis (degree o m)) := by
  have he : proj o S = ∑ m ∈ Finset.range 64, sco o S m • basis (degree o m) := by
    funext x
    simp [proj, Finset.sum_apply]
  rw [he, RHBandNorm.embed_sum _ _ (fun m => (basis_memLp (degree o m)).const_smul (sco o S m))]
  apply Finset.sum_congr rfl
  intro m _
  exact RHBandNorm.embed_smul _ _ (basis_memLp _)

lemma embed_residual (o : Bool) (S : ℝ → ℝ) (hS : MemLp S 2 volume) :
    embed (fun x => S x - proj o S x) =
      embed S - ∑ m ∈ Finset.range 64, sco o S m • embed (basis (degree o m)) := by
  change embed (S - proj o S) = _
  rw [RHBandNorm.embed_sub _ _ hS (proj_memLp o S), embed_proj]

/-- Pythagoras for the finite fixed-parity projection, in real Lebesgue integrals. -/
theorem projection_norm (o : Bool) (S : ℝ → ℝ) (hS : MemLp S 2 volume) :
    (∫ x, (S x - proj o S x)^2) = (∫ x, (S x)^2) -
      ∑ m ∈ Finset.range 64, (sco o S m)^2 := by
  let v : Fin 64 → H := fun m => embed (basis (degree o m))
  have hv (i j : Fin 64) : inner ℝ (v i) (v j) = if i = j then (1:ℝ) else 0 := by
    have he := RHResidualApprox0494.e_orthonormal o i (Finset.mem_range.mpr i.isLt)
      j (Finset.mem_range.mpr j.isLt)
    simpa only [v, Fin.ext_iff] using he
  have hi (m : Fin 64) : inner ℝ (v m) (embed S) = sco o S m :=
    sco_inner o S hS m
  have h := RHBandNorm.projection_norm v (embed S) hv
  simp_rw [hi] at h
  simp only [v] at h
  rw [Fin.sum_univ_eq_sum_range (fun m => sco o S m ^ 2) 64,
    Fin.sum_univ_eq_sum_range (fun m => sco o S m • embed (basis (degree o m))) 64] at h
  rw [← embed_residual o S hS,
    RHStepA1G1.embed_norm_sq _ (residual_memLp o S hS),
    RHStepA1G1.embed_norm_sq S hS] at h
  linarith

/-- Expanded contract: the coefficients are exactly the Lebesgue integrals of S times basis. -/
theorem projection_identity (o : Bool) (S : ℝ → ℝ) (hS : MemLp S 2 volume) :
    (∫ x, (S x - ∑ m ∈ Finset.range 64,
      (∫ y, S y * basis (degree o m) y) * basis (degree o m) x)^2) =
    (∫ x, (S x)^2) - ∑ m ∈ Finset.range 64,
      (∫ y, S y * basis (degree o m) y)^2 := by
  simpa only [proj, sco] using projection_norm o S hS

end RHProjection0525

/- Source: Parity0525.lean -/

open MeasureTheory

namespace RHParity0525

/-- Reflection preserves the real Lebesgue L² domain. -/
lemma memLp_reflect {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    MemLp (fun x => g (-x)) 2 volume := by
  simpa only [Function.comp_def] using
    hg.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Reflect an a.e. equality without asserting pointwise equality. -/
lemma ae_eq_reflect {g h : ℝ → ℝ} (hgh : g =ᵐ[volume] h) :
    (fun x => g (-x)) =ᵐ[volume] (fun x => h (-x)) := by
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hgh

noncomputable def parityAverage (ε : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (g x + ε * g (-x)) / 2

lemma memLp_parityAverage {g : ℝ → ℝ} (hg : MemLp g 2 volume) (ε : ℝ) :
    MemLp (parityAverage ε g) 2 volume := by
  have he : parityAverage ε g = fun x => (1/2:ℝ) * (g x + ε * g (-x)) := by
    funext x
    unfold parityAverage
    ring
  rw [he]
  exact (hg.add ((memLp_reflect hg).const_mul ε)).const_mul (1/2:ℝ)

lemma average_sq_le (a b ε : ℝ) (hε : ε ^ 2 = 1) :
    ((a + ε * b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : ((a + ε * b) / 2) ^ 2 ≤ (a ^ 2 + (ε*b) ^ 2) / 2 := by
    nlinarith [sq_nonneg (a - ε*b)]
  simpa only [mul_pow, hε, one_mul] using h

/-- Reflection averaging is a contraction for squared L² integrals. -/
theorem integral_parityAverage_sq_le {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    {ε : ℝ} (hε : ε ^ 2 = 1) :
    (∫ x, ((g x + ε * g (-x)) / 2) ^ 2) ≤ ∫ x, (g x) ^ 2 := by
  have hr := memLp_reflect hg
  have ht := (memLp_parityAverage hg ε).integrable_sq
  have hu : Integrable (fun x => ((g x)^2 + (g (-x))^2)/2) volume :=
    (hg.integrable_sq.add hr.integrable_sq).div_const 2
  calc
    (∫ x, ((g x + ε * g (-x)) / 2) ^ 2) ≤
        ∫ x, ((g x)^2 + (g (-x))^2)/2 :=
      integral_mono ht hu (fun x => average_sq_le (g x) (g (-x)) ε hε)
    _ = ∫ x, (g x)^2 := by
      rw [integral_div, integral_add hg.integrable_sq hr.integrable_sq]
      have hneg : (∫ x : ℝ, (g (-x))^2) = ∫ x : ℝ, (g x)^2 :=
        integral_neg_eq_self (fun x : ℝ => (g x)^2) volume
      rw [hneg]
      ring

end RHParity0525


/- Source: ColumnPoly0525.lean -/

/-! Finite weighted ClaimA, with the same open-window a.e. error statement.
The weights are arbitrary real numbers; no positivity or invertibility is assumed. -/

open MeasureTheory Set
open scoped BigOperators
namespace RHColumnPoly0525
open RHConditionalLog5 RHLog5Bridge RHInterface0516

/-- Exact finite-column contract. The nonnegative-error hypothesis is retained. -/
theorem weighted_claimA (δ : ℝ) (hδ : 0 ≤ δ) (hA : ClaimA δ)
    (o : Bool) (b : I → ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 127 ∧
      ∀ᵐ x ∂(volume : Measure ℝ), |x| < halfWidth →
        |(∑ i : I, b i * col o i x) +
          (∑ i : I, b i * Sx (degree o i) x) - P.eval x| ≤
            δ * ∑ i : I, |b i| := by
  classical
  choose Q hQdeg hQae using hA o
  let P : Polynomial ℝ := ∑ i : I, Polynomial.C (b i) * Q i
  have hPdeg : P.natDegree ≤ 127 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_C_mul_le (b i) (Q i)).trans (hQdeg i)
  have hPeval (x : ℝ) : P.eval x = ∑ i : I, b i * (Q i).eval x := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  refine ⟨P, hPdeg, ?_⟩
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ i : I,
      |x| < halfWidth → |col o i x + Sx (degree o i) x - (Q i).eval x| ≤ δ :=
    ae_all_iff.mpr hQae
  filter_upwards [hall] with x hx
  intro hxL
  have he : (∑ i : I, b i * col o i x) +
      (∑ i : I, b i * Sx (degree o i) x) - P.eval x =
      ∑ i : I, b i * (col o i x + Sx (degree o i) x - (Q i).eval x) := by
    rw [hPeval]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [he]
  exact RHError0525.weighted_error b
    (fun i => col o i x + Sx (degree o i) x - (Q i).eval x) δ (fun i => hx i hxL)

lemma not_abs_lt_of_outside {x : ℝ} (hx : x ∉ Icc (-halfWidth) halfWidth) :
    ¬ |x| < halfWidth := by
  intro h
  exact hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

lemma col_zero_outside (o : Bool) (i : I) {x : ℝ}
    (hx : x ∉ Icc (-halfWidth) halfWidth) : col o i x = 0 := by
  simp only [col, RHWeilColumnCandidate.column, if_neg (not_abs_lt_of_outside hx)]

lemma Sx_zero_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-halfWidth) halfWidth) : Sx n x = 0 := by
  simp only [Sx, if_neg (not_abs_lt_of_outside hx)]

lemma zeroPoly_zero_outside (P : Polynomial ℝ) {x : ℝ}
    (hx : x ∉ Icc (-halfWidth) halfWidth) :
    RHWeilColumnCandidate.zeroPoly halfWidth P x = 0 := by
  exact Set.indicator_of_notMem hx _

end RHColumnPoly0525

/- Source: AssemblyCore0525.lean -/

open MeasureTheory Set Finset
open scoped BigOperators
namespace RHAssemblyCore0525
open RHConditionalLog5 RHLog5Bridge RHWeilColumnCandidate RHProjection0525

lemma basis_parity (o : Bool) (m : ℕ) (x : ℝ) :
    basis (degree o m) (-x) = (-1)^(if o then 1 else 0) * basis (degree o m) x := by
  have h := RHColParity0520.zeroPoly_parity halfWidth ((-1:ℝ)^(degree o m))
    (basisPoly (degree o m)) (RHPrRed0511.bparity (degree o m)) x
  have he : (-1:ℝ)^(degree o m) = (-1)^(if o then 1 else 0) := by
    cases o <;> simp [degree, pow_add, pow_mul]
  simpa only [basis, he] using h

lemma proj_parity (o : Bool) (S : ℝ → ℝ) (x : ℝ) :
    proj o S (-x) = (-1)^(if o then 1 else 0) * proj o S x := by
  unfold proj
  simp_rw [basis_parity]
  rw [mul_sum]
  exact sum_congr rfl (fun m _ => by ring)

lemma zeroPoly_parity_expansion (P : Polynomial ℝ) (hP : P.natDegree ≤ 127) (o : Bool) :
    ∃ c : ℕ → ℝ, ∀ x,
      (zeroPoly halfWidth P x + (-1)^(if o then 1 else 0) * zeroPoly halfWidth P (-x))/2 =
        ∑ m ∈ range 64, c m * basis (degree o m) x := by
  obtain ⟨c, hc⟩ := RHPolyExp0522.poly_parity P hP o
  refine ⟨c, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · have hn := (RHColParity0520.mem_neg halfWidth x).mpr hx
    simpa only [zeroPoly, basis, indicator_of_mem hx, indicator_of_mem hn] using hc x
  · have hn := mt (RHColParity0520.mem_neg halfWidth x).mp hx
    simp only [zeroPoly, basis, indicator_of_notMem hx, indicator_of_notMem hn,
      mul_zero, add_zero, zero_div, sum_const_zero]

/-- General real L² assembly, requiring no support or parity condition on S. -/
theorem exists_approx (o : Bool) (f S : ℝ → ℝ)
    (hf : MemLp f 2 volume) (hS : MemLp S 2 volume)
    (hfpar : ∀ᵐ x ∂(volume : Measure ℝ),
      f (-x) = (-1)^(if o then 1 else 0) * f x)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ 127)
    (η : ℝ) (hη : 0 < η) (E : ℝ)
    (hE : (∫ x, (f x + S x - zeroPoly halfWidth P x)^2) ≤ E) :
    ∃ W : ℕ → ℝ,
      (∫ x, (f x - ∑ m ∈ range 64, W m * basis (degree o m) x)^2) ≤
        (1+η)*((∫ x, S x^2) - ∑ m ∈ range 64,
          (∫ x, S x * basis (degree o m) x)^2) + (1+1/η)*E := by
  let ε : ℝ := (-1)^(if o then 1 else 0)
  have hε : ε^2 = 1 := by cases o <;> norm_num [ε]
  let q : ℝ → ℝ := zeroPoly halfWidth P
  let g : ℝ → ℝ := fun x => f x - q x + proj o S x
  have hq : MemLp q 2 volume := RHColL2.zeroPoly_memLp halfWidth halfWidth_pos.le P
  have hg : MemLp g 2 volume := (hf.sub hq).add (proj_memLp o S)
  obtain ⟨c, hc⟩ := zeroPoly_parity_expansion P hP o
  refine ⟨fun m => c m - sco o S m, ?_⟩
  have he : (fun x => f x - ∑ m ∈ range 64, (c m - sco o S m)*basis (degree o m) x) =ᵐ[volume]
      fun x => (g x + ε*g (-x))/2 := by
    filter_upwards [hfpar] with x hx
    have hfav : (f x + ε*f (-x))/2 = f x := by
      change f (-x) = ε*f x at hx
      rw [hx, ← mul_assoc, ← pow_two, hε, one_mul]
      ring
    have hpav : (proj o S x + ε*proj o S (-x))/2 = proj o S x := by
      rw [proj_parity]
      change (proj o S x + ε*(ε*proj o S x))/2 = _
      rw [← mul_assoc, ← pow_two, hε, one_mul]
      ring
    have hcx : (q x + ε*q (-x))/2 = ∑ m ∈ range 64, c m*basis (degree o m) x := hc x
    have hs : (∑ m ∈ range 64, (c m-sco o S m)*basis (degree o m) x) =
        (∑ m ∈ range 64, c m*basis (degree o m) x) - proj o S x := by
      simp only [sub_mul, sum_sub_distrib, proj]
    rw [hs]
    dsimp only [g]
    linear_combination -hfav + hcx - hpav
  have hi : (∫ x, (f x - ∑ m ∈ range 64, (c m-sco o S m)*basis (degree o m) x)^2) ≤
      ∫ x, (g x)^2 := by
    calc
      _ = ∫ x, ((g x + ε*g (-x))/2)^2 := integral_congr_ae (he.fun_comp (fun z => z^2))
      _ ≤ _ := RHParity0525.integral_parityAverage_sq_le hg hε
  let a : ℝ → ℝ := fun x => f x + S x - q x
  let b : ℝ → ℝ := fun x => S x - proj o S x
  have ha : MemLp a 2 volume := (hf.add hS).sub hq
  have hb : MemLp b 2 volume := residual_memLp o S hS
  have hy := RHError0525.integral_young_sub a b ha hb η hη
  have hge : (fun x => (g x)^2) = fun x => (a x-b x)^2 := by
    funext x
    dsimp only [g, a, b]
    ring
  have heA : (∫ x, (a x)^2) ≤ E := hE
  have hcoef : 0 ≤ 1+1/η := by positivity
  calc
    _ ≤ ∫ x, (g x)^2 := hi
    _ = ∫ x, (a x-b x)^2 := congrArg (fun v : ℝ → ℝ => ∫ x, v x) hge
    _ ≤ (1+1/η)*(∫ x, (a x)^2)+(1+η)*(∫ x, (b x)^2) := hy
    _ ≤ (1+1/η)*E+(1+η)*(∫ x, (b x)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left heA hcoef) (le_refl _)
    _ = _ := by
      dsimp only [b]
      rw [projection_norm o S hS]
      unfold sco
      ring

end RHAssemblyCore0525

/- Source: Assembly0525.lean -/

open MeasureTheory Set Finset
open scoped BigOperators
namespace RHAssembly0525
open RHConditionalLog5 RHLog5Bridge RHInterface0516

/-- Supplies the analytic input to the fixed 0524 numeric interface. -/
theorem assembly : RHInterface0524.AssemblyGoal := by
  classical
  intro δ η τ hδ hη hA hpar hNum o
  let b : I → I → ℝ := fun j i => RHConcreteParameters.concrete.B o i j
  have hcol : ∀ i : I, MemLp (col o i) 2 volume := RHResidualApprox0494.col_memLp o
  have hsx : ∀ i : I, MemLp (Sx (degree o i)) 2 volume := fun i => RHSxLp0525.Sx_memLp _
  have perj (j : I) : ∃ w : ℕ → ℝ,
      (∫ x, ((∑ i : I, b j i*col o i x)-
        ∑ m ∈ range 64, w m*basis (degree o m) x)^2) ≤
      (1+η)*(∑ i : I, ∑ k : I, b j i*b j k*RHInterface0524.Gam o i k-
        ∑ m ∈ range 64, (∑ i : I, b j i*RHInterface0524.sco o i m)^2)+
      (1+1/η)*(2*halfWidth)*(δ*∑ i : I, |b j i|)^2 := by
    let f : ℝ → ℝ := fun x => ∑ i : I, b j i*col o i x
    let S : ℝ → ℝ := fun x => ∑ i : I, b j i*Sx (degree o i) x
    have hf : MemLp f 2 volume := RHGram0525.sum_memLp _ hcol (b j)
    have hS : MemLp S 2 volume := RHGram0525.sum_memLp _ hsx (b j)
    obtain ⟨P,hP,hclose⟩ := RHColumnPoly0525.weighted_claimA δ hδ hA o (b j)
    let q := RHWeilColumnCandidate.zeroPoly halfWidth P
    have hbound : (∫ x, (f x+S x-q x)^2) ≤
        2*halfWidth*(δ*∑ i : I, |b j i|)^2 := by
      apply RHUniform0525.bounded_sq _ _ _ halfWidth_pos.le (by positivity)
      · intro x hx
        have hfz : f x = 0 := by
          simp only [f, RHColumnPoly0525.col_zero_outside o _ hx, mul_zero, sum_const_zero]
        have hsz : S x = 0 := by
          simp only [S, RHColumnPoly0525.Sx_zero_outside _ hx, mul_zero, sum_const_zero]
        rw [hfz,hsz]
        dsimp only [q]
        rw [RHColumnPoly0525.zeroPoly_zero_outside P hx]
        ring
      · filter_upwards [hclose, Measure.ae_ne volume (-halfWidth), Measure.ae_ne volume halfWidth]
          with x hx hn hp
        intro hxi
        have hxi' : |x| < halfWidth := abs_lt.mpr
          ⟨lt_of_le_of_ne hxi.1 (Ne.symm hn),lt_of_le_of_ne hxi.2 hp⟩
        simpa only [f,S,q,RHWeilColumnCandidate.zeroPoly,Set.indicator_of_mem hxi] using hx hxi'
    have hfp : ∀ᵐ x ∂volume, f (-x)=(-1)^(if o then 1 else 0)*f x := by
      have hall := ae_all_iff.mpr (hpar o)
      filter_upwards [hall] with x hx
      dsimp [f]
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [hx i]
      have he : (-1:ℝ)^(degree o i)=(-1)^(if o then 1 else 0) := by
        cases o <;> simp [degree,pow_add,pow_mul]
      rw [he]
      ring
    obtain ⟨w,hw⟩ := RHAssemblyCore0525.exists_approx o f S hf hS hfp P hP η hη
      (2*halfWidth*(δ*∑ i : I, |b j i|)^2) hbound
    refine ⟨w, ?_⟩
    have hg : (∫ x, S x^2) = ∑ i : I, ∑ k : I, b j i*b j k*RHInterface0524.Gam o i k :=
      RHGram0525.gram_sum _ hsx (b j)
    have hc (m : ℕ) : (∫ x, S x*basis (degree o m) x)=
        ∑ i : I, b j i*RHInterface0524.sco o i m :=
      RHGram0525.sum_inner _ hsx (b j) _ (RHResidualMembership.basis_memLp _)
    rw [hg] at hw
    simp_rw [hc] at hw
    convert hw using 1 <;> ring
  choose W hW using perj
  refine ⟨fun m j => W j m, ?_⟩
  apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => hW j))
    (by have := dM_pos o; positivity))
  exact hNum o

end RHAssembly0525
