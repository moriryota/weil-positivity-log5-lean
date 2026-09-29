import Final
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
namespace RHFiniteProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma finite_span_le {ι : Type*} (D : Submodule ℂ E) (s : Finset ι) (e : ι → E)
    (he : ∀ i ∈ s, e i ∈ D) : Submodule.span ℂ (e '' (s : Set ι)) ≤ D := by
  apply Submodule.span_le.mpr
  rintro v ⟨i,hi,rfl⟩
  exact he i hi

/-- The genuine orthogonal projection onto the finite span. It requires no
orthonormality of the spanning family and no closedness of D. -/
noncomputable def finiteProjection {ι : Type*} (s : Finset ι) (e : ι → E) : E →L[ℂ] E := by
  let S := Submodule.span ℂ (e '' (s : Set ι))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image e)
  exact S.starProjection

lemma finiteProjection_mem {ι : Type*} (D : Submodule ℂ E) (s : Finset ι) (e : ι → E)
    (he : ∀ i ∈ s, e i ∈ D) (f : E) : finiteProjection s e f ∈ D := by
  let S := Submodule.span ℂ (e '' (s : Set ι))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image e)
  change S.starProjection f ∈ D
  exact finite_span_le D s e he (S.starProjection_apply_mem f)

lemma finiteProjection_residual_mem {ι : Type*} (D : Submodule ℂ E) (s : Finset ι) (e : ι → E)
    (he : ∀ i ∈ s, e i ∈ D) {f : E} (hf : f ∈ D) : f-finiteProjection s e f ∈ D :=
  D.sub_mem hf (finiteProjection_mem D s e he f)

end RHFiniteProjection
