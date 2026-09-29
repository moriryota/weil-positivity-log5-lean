import RealCoefficientBridge
import RealEmbedding
open MeasureTheory Set
open scoped BigOperators
namespace RHResidualMembership
open RHConditionalLog5 RHLog5Bridge RHRealBasisBridge RHRealCoefficientBridge
lemma basis_memLp (n : ℕ) : MemLp (basis n) 2 volume := by
  have hp := RHBoundedWindow.polynomial_memLp halfWidth_pos.le
    (RHLegendreDirections.directionPoly halfWidth n)
  have hc : MemLp (fun x => (basis n x : ℂ)) 2 volume := by
    simp_rw [basis_complex]
    exact (memLp_indicator_iff_restrict measurableSet_Icc).mpr hp
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.comp_memLp' hc
lemma basis_zero_outside (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (-halfWidth) halfWidth) : basis n x = 0 := by
  simp [basis, RHWeilColumnCandidate.zeroPoly, hx]
lemma low_memLp (o : Bool) (u : ℝ → ℝ) : MemLp (low o u) 2 volume := by
  classical
  exact memLp_finsetSum' Finset.univ (fun i _ =>
    (basis_memLp (degree o i)).const_smul (alpha o u i))
lemma low_zero_outside (o : Bool) (u : ℝ → ℝ) (x : ℝ)
    (hx : x ∉ Icc (-halfWidth) halfWidth) : low o u x = 0 := by
  simp [low, basis_zero_outside _ x hx]
lemma component_zero_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ)
    (hx : x ∉ Icc (-halfWidth) halfWidth) : component o u x = 0 := by
  by_contra hn
  exact hx (abs_le.mp (RHG3RealEmbedding.component_support o u hu x hn))
lemma tail_memLp (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    MemLp (tail o u) 2 volume :=
  (RHG3RealEmbedding.component_memLp o u hu).sub (low_memLp o u)
lemma tail_zero_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ)
    (hx : x ∉ Icc (-halfWidth) halfWidth) : tail o u x = 0 := by
  simp [tail, component_zero_outside o u hu x hx, low_zero_outside o u x hx]
noncomputable def farFunction (o : Bool) (u : ℝ → ℝ) : ℝ → ℝ :=
  tail o u - ∑ i : I, band o u i • basis (degree o (32+i))
lemma farFunction_memLp (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    MemLp (farFunction o u) 2 volume := by
  classical
  exact (tail_memLp o u hu).sub (memLp_finsetSum' Finset.univ
    (fun i _ => (basis_memLp (degree o (32+i))).const_smul (band o u i)))
lemma farFunction_zero_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ)
    (hx : x ∉ Icc (-halfWidth) halfWidth) : farFunction o u x = 0 := by
  simp [farFunction, tail_zero_outside o u hu x hx, basis_zero_outside _ x hx]
lemma tail_inner (o : Bool) (u : ℝ → ℝ) (hu : Test u) (n : ℕ) :
    inner ℂ (RHLegendreDirections.direction halfWidth halfWidth_pos.le n)
      (intervalEmbed (tail o u) (tail_memLp o u hu)) = (coeff (tail o u) n : ℂ) :=
  inner_intervalEmbed _ _ n
lemma tail_norm (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖intervalEmbed (tail o u) (tail_memLp o u hu)‖ = ‖embed (tail o u)‖ :=
  norm_intervalEmbed _ _ (tail_zero_outside o u hu)
lemma far_norm (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖intervalEmbed (farFunction o u) (farFunction_memLp o u hu)‖ = ‖far o u‖ :=
  norm_intervalEmbed _ _ (farFunction_zero_outside o u hu)
end RHResidualMembership
