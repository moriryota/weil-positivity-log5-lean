import FiniteProjection
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped BigOperators
namespace RHFiniteProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Reuse Mathlib's finite orthonormal-basis projection formula. The hypothesis
is explicit; this does not prove orthonormality of the concrete Legendre family. -/
theorem finiteProjection_eq_sum {ι : Type*} (s : Finset ι) (e : ι → E)
    (he : Orthonormal ℂ e) (f : E) :
    finiteProjection s e f = ∑ i ∈ s, inner ℂ (e i) f • e i := by
  classical
  let S := Submodule.span ℂ ((s.image e : Finset E) : Set E)
  let b : OrthonormalBasis s ℂ S := OrthonormalBasis.span he s
  have hb (i : s) : ((b i : S) : E) = e i := OrthonormalBasis.span_apply he s i
  have h := b.orthogonalProjectionOnto_apply_eq_sum f
  have hc := congrArg (fun z : S => (z : E)) h
  have hp : finiteProjection s e f = S.starProjection f := by
    simp only [finiteProjection, S, Finset.coe_image]
  rw [hp]
  simp only [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_sum,
    Submodule.coe_smul, hb] at hc
  have hsum := Finset.sum_coe_sort s (fun i => inner ℂ (e i) f • e i)
  exact hc.trans hsum

end RHFiniteProjection
