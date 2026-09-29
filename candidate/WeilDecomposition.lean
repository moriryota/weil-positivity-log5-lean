import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RHWeilDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quadratic form from a symmetric bilinear form: Q(x) = B x x. -/
def quad_of_bilin (B : LinearMap.BilinForm ℝ E) (x : E) : ℝ :=
  B x x

/-- Decomposition of a quadratic form into low-degree, cross, and residual components:
Q(p + r) = Q(p) + 2 * B p r + Q(r)
for any symmetric bilinear form. -/
theorem quad_add_split (B : LinearMap.BilinForm ℝ E)
    (h_symm : ∀ x y, B x y = B y x) (p r : E) :
    quad_of_bilin B (p + r) =
      quad_of_bilin B p + 2 * B p r + quad_of_bilin B r := by
  unfold quad_of_bilin
  have h1 : B (p + r) (p + r) = B p (p + r) + B r (p + r) := by
    exact LinearMap.BilinForm.add_left (R := ℝ) (M := E) p r (p + r)
  have h2 : B p (p + r) = B p p + B p r := by
    exact LinearMap.BilinForm.add_right (R := ℝ) (M := E) p p r
  have h3 : B r (p + r) = B r p + B r r := by
    exact LinearMap.BilinForm.add_right (R := ℝ) (M := E) r p r
  rw [h1, h2, h3, h_symm r p]
  ring

/-- Finite linear combination expansion for the low block:
p = ∑ j ∈ s, a j • phi j implies
B(p, r) = ∑ j ∈ s, a j * B(phi j, r). -/
theorem bilin_linear_combination {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : LinearMap.BilinForm ℝ E) (a : ι → ℝ) (phi : ι → E) (r : E) :
    B (∑ j ∈ s, a j • phi j) r = ∑ j ∈ s, a j * B (phi j) r := by
  induction' s using Finset.induction_on with i s hi ih
  · simp only [Finset.sum_empty, LinearMap.BilinForm.zero_left]
  · rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hadd : B (a i • phi i + ∑ j ∈ s, a j • phi j) r =
        B (a i • phi i) r + B (∑ j ∈ s, a j • phi j) r := by
      exact LinearMap.BilinForm.add_left (R := ℝ) (M := E) (a i • phi i) _ r
    have hsmul : B (a i • phi i) r = a i * B (phi i) r := by
      exact LinearMap.BilinForm.smul_left (R := ℝ) (M := E) (a i) (phi i) r
    rw [hadd, hsmul, ih]

/-- Cross term representation via dual action vectors:
If for each basis element phi j there exists an action vector g j ∈ E such that
B(phi j, r) = inner ℝ (g j) r,
then the cross term is an exact Hilbert inner product:
B(p, r) = inner ℝ (∑ j ∈ s, a j • g j) r. -/
theorem cross_term_as_inner {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : LinearMap.BilinForm ℝ E) (a : ι → ℝ) (phi g : ι → E) (r : E)
    (h_rep : ∀ j ∈ s, B (phi j) r = inner ℝ (g j) r) :
    B (∑ j ∈ s, a j • phi j) r = inner ℝ (∑ j ∈ s, a j • g j) r := by
  rw [bilin_linear_combination s B a phi r]
  have h_inner_sum : inner ℝ (∑ j ∈ s, a j • g j) r = ∑ j ∈ s, a j * inner ℝ (g j) r := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [real_inner_smul_left]
  rw [h_inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h_rep j hj]

/-- Combined Weil form decomposition:
For f = p + r with p = ∑ j ∈ s, a j • phi j and g j representing the action of phi j on r,
Q(f) = Q(p) + 2 * ⟨∑ a j • g j, r⟩ + Q(r). -/
theorem weil_decomposition {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (B : LinearMap.BilinForm ℝ E) (h_symm : ∀ x y, B x y = B y x)
    (a : ι → ℝ) (phi g : ι → E) (r : E)
    (h_rep : ∀ j ∈ s, B (phi j) r = inner ℝ (g j) r) :
    quad_of_bilin B ((∑ j ∈ s, a j • phi j) + r) =
      quad_of_bilin B (∑ j ∈ s, a j • phi j) +
      2 * inner ℝ (∑ j ∈ s, a j • g j) r +
      quad_of_bilin B r := by
  have hsplit := quad_add_split B h_symm (∑ j ∈ s, a j • phi j) r
  rw [cross_term_as_inner s B a phi g r h_rep] at hsplit
  exact hsplit

end RHWeilDecomposition

