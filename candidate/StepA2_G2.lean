import ConditionalLog5
import ConcreteParameters
import ResidualMembership
import TestStepA1
import WeilColumnCandidate
import TargetFormBinding
import ResidualCertificate
import ColL2Components
import BandNorm
import RealLowZero
import TailSupport
import OutsideIntegral

open MeasureTheory Set
open scoped Matrix BigOperators
open RHConditionalLog5 RHResidualMembership RHConcreteParameters RHWeilColumnCandidate RHTargetFormBinding RHResidualCertificate RHColL2 RHBandNorm RHRealLowZero RHLog5Bridge RHAutocorrEnergy RH_LiteratureBridge RHPoleParity RHExternalPotential

namespace RHStepA2G2

/-- Column L^2 integrability hypothesis on the fundamental domain. -/
def ColMemLp : Prop := ∀ o i, MemLp (col o i) 2 volume

/-- Column L^2 integrability is completely unconditional. -/
theorem col_memLp_unconditional : ColMemLp := by
  intro o i
  dsimp [col]
  exact column_memLp_unconditional halfWidth halfWidth_pos (basisPoly (degree o i))

/-- Part 1 of G2: column L^2 integrability and project-64 difference integrability. -/
theorem g2_part1_of_col_memLp (h_col : ColMemLp) :
    (∀ o i, MemLp (col o i) 2 volume ∧ MemLp (col o i - project o 64 (col o i)) 2 volume) := by
  intro o i
  have h := h_col o i
  exact ⟨h, h.sub (project_memLp o 64 (col o i))⟩

/-- Unconditional Part 1 of G2. -/
theorem g2_part1_unconditional :
    (∀ o i, MemLp (col o i) 2 volume ∧ MemLp (col o i - project o 64 (col o i)) 2 volume) :=
  g2_part1_of_col_memLp col_memLp_unconditional

/-- Coordinate reduction: P.B * P.coordinates rewrites directly to alpha by coordinates_identity. -/
theorem g2_rhs_coordinates_reduction (o : Bool) (u : ℝ → ℝ) :
    (∑ i : I, mixed o u i * band o u i) +
      inner ℝ (residual_vector (columnResidual o) (concrete.B o *ᵥ concrete.coordinates o u)) (far o u) =
    (∑ i : I, mixed o u i * band o u i) +
      inner ℝ (residual_vector (columnResidual o) (alpha o u)) (far o u) := by
  rw [RHConcreteParameters.coordinates_identity o u]

/-- The bilinear mixed Weil representation hypothesis for the concrete alpha coordinates. -/
def G2BilinearRepresentation : Prop := ∀ o u, Test u →
  (targetQ_real (component o u) - targetQ_real (low o u) - targetQ_real (tail o u)) / 2 =
    (∑ i : I, mixed o u i * band o u i) +
    inner ℝ (residual_vector (columnResidual o) (alpha o u)) (far o u)

/-- Sector-wise representation hypotheses. -/
def G2EvenRepresentation : Prop := ∀ u, Test u →
  (targetQ_real (component false u) - targetQ_real (low false u) - targetQ_real (tail false u)) / 2 =
    (∑ i : I, mixed false u i * band false u i) +
    inner ℝ (residual_vector (columnResidual false) (alpha false u)) (far false u)

def G2OddRepresentation : Prop := ∀ u, Test u →
  (targetQ_real (component true u) - targetQ_real (low true u) - targetQ_real (tail true u)) / 2 =
    (∑ i : I, mixed true u i * band true u i) +
    inner ℝ (residual_vector (columnResidual true) (alpha true u)) (far true u)

/-- Equivalence of combined representation and sector-wise representations. -/
theorem g2_representation_iff :
    G2BilinearRepresentation ↔ (G2EvenRepresentation ∧ G2OddRepresentation) := by
  constructor
  · intro h
    exact ⟨fun u hu => h false u hu, fun u hu => h true u hu⟩
  · rintro ⟨h_even, h_odd⟩ o u hu
    cases o
    · exact h_even u hu
    · exact h_odd u hu

/-- G2 transfer theorem: column L^2 integrability together with the bilinear mixed representation
    strictly implies G2 for concrete parameters. -/
theorem g2_of_components
    (h_col : ColMemLp)
    (h_rep : G2BilinearRepresentation) :
    G2 concrete := by
  refine ⟨g2_part1_of_col_memLp h_col, ?_⟩
  intro o u hu
  rw [g2_rhs_coordinates_reduction o u]
  exact h_rep o u hu

/-- Sector-wise G2 transfer theorem. -/
theorem g2_of_sector_representation
    (h_col : ColMemLp)
    (h_even : G2EvenRepresentation)
    (h_odd : G2OddRepresentation) :
    G2 concrete :=
  g2_of_components h_col (g2_representation_iff.mpr ⟨h_even, h_odd⟩)

/-- G2 transfer theorem with unconditional column L^2 integrability:
    only the bilinear mixed representation is required to conclude G2 concrete. -/
theorem g2_of_representation
    (h_rep : G2BilinearRepresentation) :
    G2 concrete :=
  g2_of_components col_memLp_unconditional h_rep

/-- Sector-wise G2 transfer theorem with unconditional column integrability. -/
theorem g2_of_sector_representation_unconditional
    (h_even : G2EvenRepresentation)
    (h_odd : G2OddRepresentation) :
    G2 concrete :=
  g2_of_representation (g2_representation_iff.mpr ⟨h_even, h_odd⟩)

/-- Inner product expansion of the residual vector term. -/
theorem residual_inner_expansion (o : Bool) (u : ℝ → ℝ) :
    inner ℝ (residual_vector (columnResidual o) (alpha o u)) (far o u) =
      ∑ j : I, alpha o u j * inner ℝ (columnResidual o j) (far o u) := by
  unfold residual_vector
  rw [real_inner_comm, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_right, real_inner_comm (far o u)]

/-- Complete algebraic rearrangement of the G2 right-hand side into alpha-linear combination. -/
theorem g2_rhs_sum_expansion (o : Bool) (u : ℝ → ℝ) :
    (∑ i : I, mixed o u i * band o u i) +
      inner ℝ (residual_vector (columnResidual o) (alpha o u)) (far o u) =
    ∑ j : I, alpha o u j * (
      (∑ i : I, band o u i * (∫ x, col o j x * basis (degree o (32+i)) x)) +
      inner ℝ (columnResidual o j) (far o u)) := by
  have h1 : (∑ i : I, mixed o u i * band o u i) =
      ∑ j : I, alpha o u j * (∑ i : I, band o u i * (∫ x, col o j x * basis (degree o (32+i)) x)) := by
    unfold mixed
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have h_assoc : ∀ x : I, (alpha o u j * ∫ (x_1 : ℝ), col o j x_1 * basis (degree o (32 + (x : ℕ))) x_1) * band o u x =
        alpha o u j * (band o u x * ∫ (x_1 : ℝ), col o j x_1 * basis (degree o (32 + (x : ℕ))) x_1) :=
      fun x => by ring
    simp_rw [h_assoc]
    rw [← Finset.mul_sum]
  rw [h1, residual_inner_expansion, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add]

lemma degree_inj (o : Bool) (m n : ℕ) : degree o m = degree o n ↔ m = n := by
  unfold degree
  constructor
  · intro h
    cases o <;> omega
  · rintro rfl; rfl

lemma far_inner_basis (o : Bool) (u : ℝ → ℝ) (hu : Test u) (k : ℕ) (hk : k < 64) :
    inner ℝ (embed (basis (degree o k))) (far o u) = 0 := by
  let v : I → H := fun i => embed (basis (degree o (32+i)))
  have hfar : far o u = embed (tail o u) - ∑ i : I, band o u i • v i := by
    unfold far
    rw [embed_sub _ _ (tail_memLp o u hu)
      (memLp_finsetSum' (Finset.univ : Finset I) (fun i _ =>
        (basis_memLp (degree o (32+i))).const_smul (band o u i)))]
    rw [embed_sum _ _ (fun (i : I) => (basis_memLp (degree o (32+i))).const_smul (band o u i))]
    simp only [embed_smul _ _ (basis_memLp _)]
    rfl
  rw [real_inner_comm, hfar, inner_sub_left]
  have h1 : inner ℝ (embed (tail o u)) (embed (basis (degree o k))) = coeff (tail o u) (degree o k) := by
    rw [real_inner_comm, basis_inner_function (degree o k) (tail o u) (tail_memLp o u hu)]
  rw [h1]
  rw [sum_inner]
  have h2 : ∀ i : I, inner ℝ (band o u i • v i) (embed (basis (degree o k))) =
      band o u i * if degree o (32+(i:ℕ)) = degree o k then 1 else 0 := by
    intro i
    dsimp [v]
    rw [real_inner_smul_left, basis_inner]
  simp_rw [h2, degree_inj]
  by_cases hk32 : k < 32
  · have h0 : coeff (tail o u) (degree o k) = 0 := tail_low_zero o u hu k hk32
    rw [h0]
    have hsum0 : (∑ i : I, band o u i * if 32 + (i : ℕ) = k then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : 32 + (i : ℕ) ≠ k := by omega
      simp [this]
    rw [hsum0, sub_zero]
  · have hk_ge : 32 ≤ k := not_lt.mp hk32
    have hj_lt : k - 32 < 32 := by omega
    let j : I := ⟨k - 32, hj_lt⟩
    have hkj : k = 32 + (j : ℕ) := by
      dsimp [j]
      omega
    have hband : coeff (tail o u) (degree o k) = band o u j := by
      nth_rw 1 [hkj]
      rfl
    rw [hband]
    have hsum : (∑ i : I, band o u i * if 32 + (i : ℕ) = k then 1 else 0) = band o u j := by
      rw [hkj]
      have heq (i : I) : (32 + (i : ℕ) = 32 + (j : ℕ)) ↔ i = j := by
        constructor
        · intro h; apply Fin.ext; omega
        · intro h; rw [h]
      simp_rw [heq]
      simp [Finset.sum_ite_eq']
    rw [hsum, sub_self]

lemma embed_project_64 (o : Bool) (f : ℝ → ℝ) :
    embed (project o 64 f) =
      ∑ k ∈ Finset.range 64, coeff f (degree o k) • embed (basis (degree o k)) := by
  unfold project
  rw [embed_sum]
  · apply Finset.sum_congr rfl
    intro k _
    exact embed_smul _ _ (basis_memLp _)
  · exact fun k => (basis_memLp (degree o k)).const_smul _

lemma project_64_inner_far (o : Bool) (u : ℝ → ℝ) (hu : Test u) (f : ℝ → ℝ) :
    inner ℝ (embed (project o 64 f)) (far o u) = 0 := by
  rw [embed_project_64 o f]
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_lt : k < 64 := Finset.mem_range.mp hk
  rw [real_inner_smul_left]
  have h0 := far_inner_basis o u hu k hk_lt
  rw [h0, mul_zero]

lemma columnResidual_inner_far (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    inner ℝ (columnResidual o j) (far o u) = inner ℝ (embed (col o j)) (far o u) := by
  unfold columnResidual
  have hcol : MemLp (col o j) 2 volume := col_memLp_unconditional o j
  have hproj : MemLp (project o 64 (col o j)) 2 volume := project_memLp o 64 (col o j)
  rw [embed_sub (col o j) _ hcol hproj]
  rw [inner_sub_left]
  have hp0 := project_64_inner_far o u hu (col o j)
  rw [hp0, sub_zero]

lemma far_inner_col (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) (hcol : MemLp (col o j) 2 volume) :
    inner ℝ (embed (col o j)) (far o u) =
      inner ℝ (embed (col o j)) (embed (tail o u)) -
      ∑ i : I, band o u i * (∫ x, col o j x * basis (degree o (32+i)) x) := by
  have hfar : far o u = embed (tail o u) - ∑ i : I, band o u i • embed (basis (degree o (32+i))) := by
    unfold far
    rw [embed_sub _ _ (tail_memLp o u hu)
      (memLp_finsetSum' (Finset.univ : Finset I) (fun i _ =>
        (basis_memLp (degree o (32+i))).const_smul (band o u i)))]
    rw [embed_sum _ _ (fun (i : I) => (basis_memLp (degree o (32+i))).const_smul (band o u i))]
    simp only [embed_smul _ _ (basis_memLp _)]
  rw [hfar, inner_sub_right]
  congr 1
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, inner_embed _ _ hcol (basis_memLp _)]

theorem col_far_synthesis (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    (∑ i : I, band o u i * (∫ x, col o j x * basis (degree o (32+i)) x)) +
      inner ℝ (columnResidual o j) (far o u) =
    inner ℝ (embed (col o j)) (embed (tail o u)) := by
  have hcol : MemLp (col o j) 2 volume := col_memLp_unconditional o j
  rw [columnResidual_inner_far o u hu j]
  rw [far_inner_col o u hu j hcol]
  ring

/-- Complete synthesis: the RHS of G2 reduces to the sum of inner products of col and tail. -/
theorem g2_rhs_col_tail (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∑ i : I, mixed o u i * band o u i) +
      inner ℝ (residual_vector (columnResidual o) (alpha o u)) (far o u) =
    ∑ j : I, alpha o u j * inner ℝ (embed (col o j)) (embed (tail o u)) := by
  rw [g2_rhs_sum_expansion o u]
  apply Finset.sum_congr rfl
  intro j _
  rw [col_far_synthesis o u hu j]

/-- The decomposition of component into low plus tail. -/
lemma component_eq_low_add_tail (o : Bool) (u : ℝ → ℝ) :
    component o u = fun x => low o u x + tail o u x := by
  ext x
  dsimp [tail]
  ring

/-- The left-hand side of G2 rewritten via the low plus tail decomposition. -/
lemma g2_lhs_polarization (o : Bool) (u : ℝ → ℝ) :
    (targetQ_real (component o u) - targetQ_real (low o u) - targetQ_real (tail o u)) / 2 =
      (targetQ_real (fun x => low o u x + tail o u x) - targetQ_real (low o u) - targetQ_real (tail o u)) / 2 := by
  rw [← component_eq_low_add_tail]

/-- Generic symmetric polarization form of a functional F. -/
noncomputable def polarize (F : (ℝ → ℝ) → ℝ) (f g : ℝ → ℝ) : ℝ :=
  (F (fun x => f x + g x) - F f - F g) / 2

/-- Decomposition of targetQ_real into five components: L^2, Archimedean energy, cosh, sinh, prime. -/
noncomputable def targetQ_L2 (u : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * (∫ x, (u x)^2)

noncomputable def targetQ_energy (u : ℝ → ℝ) : ℝ :=
  spatialEnergy u

noncomputable def targetQ_cosh (u : ℝ → ℝ) : ℝ :=
  2 * (∫ x, u x * Real.cosh (x / 2))^2

noncomputable def targetQ_sinh (u : ℝ → ℝ) : ℝ :=
  2 * (∫ x, u x * Real.sinh (x / 2))^2

noncomputable def targetQ_prime (u : ℝ → ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    real_autocorr u (Real.log n)

theorem targetQ_real_eq_sum (u : ℝ → ℝ) :
    targetQ_real u = targetQ_L2 u + targetQ_energy u + targetQ_cosh u - targetQ_sinh u - targetQ_prime u := by
  unfold targetQ_real targetQ_L2 targetQ_energy targetQ_cosh targetQ_sinh targetQ_prime
  ring

theorem polarize_targetQ_real (f g : ℝ → ℝ) :
    polarize targetQ_real f g =
      polarize targetQ_L2 f g +
      polarize targetQ_energy f g +
      (polarize targetQ_cosh f g - polarize targetQ_sinh f g) -
      polarize targetQ_prime f g := by
  unfold polarize
  rw [targetQ_real_eq_sum (fun x => f x + g x),
      targetQ_real_eq_sum f,
      targetQ_real_eq_sum g]
  ring

/-- The four component columns corresponding to targetQ_real components. -/
noncomputable def col_L2 (_L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * p.eval x

noncomputable def col_arch (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  (1/2:ℝ) * (∫ y in Icc (-L) L,
    RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x - p.eval y)) +
  (1/2:ℝ) * (RH_Rebaseline.T_tail (L-x) + RH_Rebaseline.T_tail (L+x)) * p.eval x

noncomputable def col_pole (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  2 * (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) * Real.cosh (x/2) -
  2 * (∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) * Real.sinh (x/2)

noncomputable def col_prime (L : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (zeroPoly L p (x-Real.log n) + zeroPoly L p (x+Real.log n))

theorem column_inner_eq_components (L : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    column_inner L p x = col_L2 L p x + col_arch L p x + col_pole L p x - col_prime L p x := by
  unfold column_inner col_L2 col_arch col_pole col_prime
  ring

/-- Almost everywhere equality of the column-tail pointwise product. -/
lemma col_tail_prod_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    (fun x => col o j x * tail o u x) =ᵐ[volume]
    (fun x => column_inner halfWidth (basisPoly (degree o j)) x * tail o u x) := by
  have h_ae : ∀ᵐ x ∂volume, |x| ≠ halfWidth := by
    have h1 : volume {halfWidth} = 0 := Real.volume_singleton
    have h2 : volume {-halfWidth} = 0 := Real.volume_singleton
    have h_sub : {x : ℝ | |x| = halfWidth} ⊆ {halfWidth} ∪ {-halfWidth} := by
      intro x (hx : |x| = halfWidth)
      obtain (h | h) := eq_or_eq_neg_of_abs_eq hx
      · exact Or.inl (Set.mem_singleton_iff.mpr h)
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
    have h_null : volume {x : ℝ | |x| = halfWidth} = 0 :=
      measure_mono_null h_sub (measure_union_null h1 h2)
    exact ae_iff.mpr (by simpa using h_null)
  filter_upwards [h_ae] with x hx
  dsimp [col]
  rw [column_eq_indicator]
  dsimp
  split_ifs with h_lt
  · rfl
  · have h_gt : |x| > halfWidth := by
      have : ¬ |x| < halfWidth := h_lt
      have : |x| ≥ halfWidth := not_lt.mp this
      exact lt_of_le_of_ne this (Ne.symm hx)
    have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
    rw [ht0, mul_zero, mul_zero]

/-- The canonical inner product between col and tail equals the integral of column_inner * tail. -/
lemma col_tail_integral_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    inner ℝ (embed (col o j)) (embed (tail o u)) =
      ∫ x, column_inner halfWidth (basisPoly (degree o j)) x * tail o u x := by
  rw [inner_embed (col o j) (tail o u) (col_memLp_unconditional o j) (tail_memLp o u hu)]
  exact integral_congr_ae (col_tail_prod_ae_eq o u hu j)

/-- Orthogonal vanishing: low and tail are strictly orthogonal in L^2. -/
lemma integral_low_tail_zero (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ∫ x, low o u x * tail o u x = 0 := by
  have hi (i : I) : Integrable (fun x => alpha o u i * (basis (degree o i) x * tail o u x)) volume :=
    ((basis_memLp (degree o i)).integrable_mul (tail_memLp o u hu)).const_mul _
  have he (x : ℝ) : low o u x * tail o u x =
      ∑ i : I, alpha o u i * (basis (degree o i) x * tail o u x) := by
    dsimp [low]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul]
  have h_coeff : (∫ x, basis (degree o i) x * tail o u x) = coeff (tail o u) (degree o i) := rfl
  rw [h_coeff, tail_low_zero o u hu i i.isLt, mul_zero]

/-- Pythagorean decomposition: integral of (low + tail)^2 equals integral of low^2 plus integral of tail^2. -/
lemma integral_low_add_tail_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∫ x, (low o u x + tail o u x)^2) = (∫ x, (low o u x)^2) + (∫ x, (tail o u x)^2) := by
  have h_low : MemLp (low o u) 2 volume := low_memLp o u
  have h_tail : MemLp (tail o u) 2 volume := tail_memLp o u hu
  have hi_low2 : Integrable (fun x => (low o u x)^2) volume := h_low.integrable_sq
  have hi_tail2 : Integrable (fun x => (tail o u x)^2) volume := h_tail.integrable_sq
  have hi_cross : Integrable (fun x => 2 * (low o u x * tail o u x)) volume :=
    (h_low.integrable_mul h_tail).const_mul 2
  have he_fun : (fun x => (low o u x + tail o u x)^2) =
      (fun x => ((low o u x)^2 + (tail o u x)^2) + 2 * (low o u x * tail o u x)) := by
    ext x; ring
  rw [he_fun]
  have hi_sum2 : Integrable (fun x => (low o u x)^2 + (tail o u x)^2) volume := hi_low2.add hi_tail2
  rw [integral_add hi_sum2 hi_cross]
  rw [integral_add hi_low2 hi_tail2]
  rw [integral_const_mul, integral_low_tail_zero o u hu, mul_zero, add_zero]

/-- Polarization of the L^2 norm term vanishes completely. -/
lemma polarize_targetQ_L2_zero (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    polarize targetQ_L2 (low o u) (tail o u) = 0 := by
  unfold polarize targetQ_L2
  rw [integral_low_add_tail_sq o u hu]
  ring

/-- The L^2 column component integral against tail vanishes identically by low-frequency orthogonality. -/
lemma col_L2_tail_integral_zero (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    (∫ x, col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x) = 0 := by
  unfold col_L2
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have h_ae : ∀ᵐ x ∂volume, (basisPoly (degree o j)).eval x * tail o u x =
      basis (degree o j) x * tail o u x := by
    have h_not (x : ℝ) (hx : |x| > halfWidth) :
        (basisPoly (degree o j)).eval x * tail o u x = basis (degree o j) x * tail o u x := by
      rw [tail_eq_zero_of_not_mem o u hu x hx, mul_zero, mul_zero]
    have h_eq : ∀ᵐ x ∂volume, |x| ≠ halfWidth := by
      have h1 : volume {halfWidth} = 0 := Real.volume_singleton
      have h2 : volume {-halfWidth} = 0 := Real.volume_singleton
      have h_sub : {x : ℝ | |x| = halfWidth} ⊆ {halfWidth} ∪ {-halfWidth} := by
        intro x (hx : |x| = halfWidth)
        obtain (h | h) := eq_or_eq_neg_of_abs_eq hx
        · exact Or.inl (Set.mem_singleton_iff.mpr h)
        · exact Or.inr (Set.mem_singleton_iff.mpr h)
      have h_null : volume {x : ℝ | |x| = halfWidth} = 0 :=
        measure_mono_null h_sub (measure_union_null h1 h2)
      exact ae_iff.mpr (by simpa using h_null)
    filter_upwards [h_eq] with x hx
    by_cases h_lt : |x| < halfWidth
    · have h_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
      unfold basis zeroPoly indicator
      simp [h_icc]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      exact h_not x h_gt
  rw [integral_congr_ae h_ae]
  have h_coeff : (∫ x, basis (degree o j) x * tail o u x) = coeff (tail o u) (degree o j) := rfl
  rw [h_coeff, tail_low_zero o u hu j j.isLt, mul_zero]

/-- The L^2 polarization identity holds unconditionally (both sides vanish). -/
def G2PolarizationL2 : Prop := ∀ o u, Test u →
  polarize targetQ_L2 (low o u) (tail o u) =
    ∑ j : I, alpha o u j * (∫ x, col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x)

theorem g2_polarization_L2_unconditional : G2PolarizationL2 := by
  intro o u hu
  rw [polarize_targetQ_L2_zero o u hu]
  have h_zeros : (∑ j : I, alpha o u j * (∫ x, col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [col_L2_tail_integral_zero o u hu j, mul_zero]
  rw [h_zeros]

lemma ae_abs_ne (L : ℝ) : ∀ᵐ x ∂volume, |x| ≠ L := by
  have h1 : volume {L} = 0 := Real.volume_singleton
  have h2 : volume {-L} = 0 := Real.volume_singleton
  have h_sub : {x : ℝ | |x| = L} ⊆ {L} ∪ {-L} := by
    intro x (hx : |x| = L)
    obtain (h | h) := eq_or_eq_neg_of_abs_eq hx
    · exact Or.inl (Set.mem_singleton_iff.mpr h)
    · exact Or.inr (Set.mem_singleton_iff.mpr h)
  have h_null : volume {x : ℝ | |x| = L} = 0 :=
    measure_mono_null h_sub (measure_union_null h1 h2)
  exact ae_iff.mpr (by simpa using h_null)

lemma integrable_mul_tail_of_restrict_memLp
    (o : Bool) (u : ℝ → ℝ) (hu : Test u) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Icc (-halfWidth) halfWidth))) :
    Integrable (fun x => g x * tail o u x) volume := by
  let g_ind := (Icc (-halfWidth) halfWidth).indicator g
  have hg_ind : MemLp g_ind 2 volume := (memLp_indicator_iff_restrict (measurableSet_Icc : MeasurableSet (Icc (-halfWidth) halfWidth))).mpr hg
  have h_tail : MemLp (tail o u) 2 volume := tail_memLp o u hu
  have hi_prod : Integrable (fun x => g_ind x * tail o u x) volume := hg_ind.integrable_mul h_tail
  have h_ae : (fun x => g x * tail o u x) =ᵐ[volume] (fun x => g_ind x * tail o u x) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · have h_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
      have hg_eq : g_ind x = g x := Set.indicator_of_mem h_icc g
      rw [hg_eq]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
      rw [ht0, mul_zero, mul_zero]
  exact hi_prod.congr h_ae.symm

lemma integrable_mul_low_of_restrict_memLp
    (o : Bool) (u : ℝ → ℝ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Icc (-halfWidth) halfWidth))) :
    Integrable (fun x => low o u x * g x) volume := by
  let g_ind := (Icc (-halfWidth) halfWidth).indicator g
  have hg_ind : MemLp g_ind 2 volume := (memLp_indicator_iff_restrict (measurableSet_Icc : MeasurableSet (Icc (-halfWidth) halfWidth))).mpr hg
  have h_low : MemLp (low o u) 2 volume := low_memLp o u
  have hi_prod : Integrable (fun x => low o u x * g_ind x) volume := h_low.integrable_mul hg_ind
  have h_ae : (fun x => low o u x * g x) =ᵐ[volume] (fun x => low o u x * g_ind x) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · have h_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
      have hg_eq : g_ind x = g x := Set.indicator_of_mem h_icc g
      rw [hg_eq]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have ht0 := low_eq_zero_of_not_mem o u x h_gt
      rw [ht0, zero_mul, zero_mul]
  exact hi_prod.congr h_ae.symm

lemma integrable_mul_basis_of_restrict_memLp
    (n : ℕ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Icc (-halfWidth) halfWidth))) :
    Integrable (fun x => basis n x * g x) volume := by
  let g_ind := (Icc (-halfWidth) halfWidth).indicator g
  have hg_ind : MemLp g_ind 2 volume := (memLp_indicator_iff_restrict (measurableSet_Icc : MeasurableSet (Icc (-halfWidth) halfWidth))).mpr hg
  have h_b : MemLp (basis n) 2 volume := basis_memLp n
  have hi_prod : Integrable (fun x => basis n x * g_ind x) volume := h_b.integrable_mul hg_ind
  have h_ae : (fun x => basis n x * g x) =ᵐ[volume] (fun x => basis n x * g_ind x) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · have h_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
      have hg_eq : g_ind x = g x := Set.indicator_of_mem h_icc g
      rw [hg_eq]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have ht0 := basis_eq_zero_of_not_mem n x h_gt
      rw [ht0, zero_mul, zero_mul]
  exact hi_prod.congr h_ae.symm

lemma col_L2_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  exact term1_memLp halfWidth halfWidth_pos.le (basisPoly (degree o j))

lemma col_arch_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  change MemLp (fun x =>
    (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y)) +
    (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (basisPoly (degree o j)).eval x) 2 (volume.restrict (Icc (-halfWidth) halfWidth))
  exact (kernel_term_memLp_unconditional halfWidth halfWidth_pos.le (basisPoly (degree o j))).add
    (tail_term_memLp halfWidth halfWidth_pos (basisPoly (degree o j)))

lemma col_pole_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => col_pole halfWidth (basisPoly (degree o j)) x * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  change MemLp (fun x =>
    2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.cosh (y/2)) * Real.cosh (x/2) -
    2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.sinh (y/2)) * Real.sinh (x/2)) 2 (volume.restrict (Icc (-halfWidth) halfWidth))
  exact (term4_memLp halfWidth (basisPoly (degree o j))).sub
    (term5_memLp halfWidth (basisPoly (degree o j)))

lemma col_prime_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => col_prime halfWidth (basisPoly (degree o j)) x * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  exact term6_memLp halfWidth halfWidth_pos.le (basisPoly (degree o j))

lemma kernel_term_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y)) * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  exact kernel_term_memLp_unconditional halfWidth halfWidth_pos.le (basisPoly (degree o j))

lemma tail_term_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (j : I) :
    Integrable (fun x => (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (basisPoly (degree o j)).eval x * tail o u x) volume := by
  apply integrable_mul_tail_of_restrict_memLp o u hu
  exact tail_term_memLp halfWidth halfWidth_pos (basisPoly (degree o j))

lemma column_linearity_integral
    (f1 f2 f3 f4 t : ℝ → ℝ)
    (h1 : Integrable (fun x => f1 x * t x) volume)
    (h2 : Integrable (fun x => f2 x * t x) volume)
    (h3 : Integrable (fun x => f3 x * t x) volume)
    (h4 : Integrable (fun x => f4 x * t x) volume) :
    (∫ x, f1 x * t x) + (∫ x, f2 x * t x) + (∫ x, f3 x * t x) - (∫ x, f4 x * t x) =
    ∫ x, (f1 x + f2 x + f3 x - f4 x) * t x := by
  have h12_int : Integrable (fun x => (f1 x + f2 x) * t x) volume := by
    have he : (fun x => (f1 x + f2 x) * t x) = (fun x => f1 x * t x + f2 x * t x) := by ext x; ring
    rw [he]
    exact h1.add h2
  have h123_int : Integrable (fun x => (f1 x + f2 x + f3 x) * t x) volume := by
    have he : (fun x => (f1 x + f2 x + f3 x) * t x) = (fun x => (f1 x + f2 x) * t x + f3 x * t x) := by ext x; ring
    rw [he]
    exact h12_int.add h3
  have he_sub : (fun x => (f1 x + f2 x + f3 x - f4 x) * t x) =
      (fun x => (f1 x + f2 x + f3 x) * t x - f4 x * t x) := by ext x; ring
  rw [he_sub]
  rw [integral_sub h123_int h4]
  have he_add2 : (fun x => (f1 x + f2 x + f3 x) * t x) =
      (fun x => (f1 x + f2 x) * t x + f3 x * t x) := by ext x; ring
  rw [he_add2]
  rw [integral_add h12_int h3]
  have he_add1 : (fun x => (f1 x + f2 x) * t x) =
      (fun x => f1 x * t x + f2 x * t x) := by ext x; ring
  rw [he_add1]
  rw [integral_add h1 h2]

/-- Component pairing hypotheses for the remaining sectors and column linearity. -/
def G2PolarizationArch : Prop := ∀ o u, Test u →
  polarize targetQ_energy (low o u) (tail o u) =
    ∑ j : I, alpha o u j * (∫ x, col_arch halfWidth (basisPoly (degree o j)) x * tail o u x)

def G2PolarizationPole : Prop := ∀ o u, Test u →
  polarize targetQ_cosh (low o u) (tail o u) - polarize targetQ_sinh (low o u) (tail o u) =
    ∑ j : I, alpha o u j * (∫ x, col_pole halfWidth (basisPoly (degree o j)) x * tail o u x)

def G2PolarizationPrime : Prop := ∀ o u, Test u →
  polarize targetQ_prime (low o u) (tail o u) =
    ∑ j : I, alpha o u j * (∫ x, col_prime halfWidth (basisPoly (degree o j)) x * tail o u x)

def G2ColumnLinearity : Prop := ∀ o u, Test u → ∀ j : I,
  (∫ x, col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x) +
  (∫ x, col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) +
  (∫ x, col_pole halfWidth (basisPoly (degree o j)) x * tail o u x) -
  (∫ x, col_prime halfWidth (basisPoly (degree o j)) x * tail o u x) =
    inner ℝ (embed (col o j)) (embed (tail o u))

/-- The column linearity identity holds unconditionally. -/
theorem g2_column_linearity_unconditional : G2ColumnLinearity := by
  intro o u hu j
  rw [col_tail_integral_eq o u hu j]
  have h1 := col_L2_mul_tail_integrable o u hu j
  have h2 := col_arch_mul_tail_integrable o u hu j
  have h3 := col_pole_mul_tail_integrable o u hu j
  have h4 := col_prime_mul_tail_integrable o u hu j
  rw [column_linearity_integral _ _ _ _ _ h1 h2 h3 h4]
  have he : (fun x => (col_L2 halfWidth (basisPoly (degree o j)) x +
      col_arch halfWidth (basisPoly (degree o j)) x +
      col_pole halfWidth (basisPoly (degree o j)) x -
      col_prime halfWidth (basisPoly (degree o j)) x) * tail o u x) =
      (fun x => column_inner halfWidth (basisPoly (degree o j)) x * tail o u x) := by
    ext x
    rw [← column_inner_eq_components]
  rw [he]

lemma integral_basis_mul_eq_setIntegral
    (n : ℕ) (g : ℝ → ℝ) :
    (∫ x, basis n x * g x) = ∫ x in Icc (-halfWidth) halfWidth, (basisPoly n).eval x * g x := by
  have h_ae : (fun x => basis n x * g x) =ᵐ[volume]
      (Icc (-halfWidth) halfWidth).indicator (fun x => (basisPoly n).eval x * g x) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · have h_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
      rw [Set.indicator_of_mem h_icc]
      unfold basis zeroPoly indicator
      simp [h_icc]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have h_not : x ∉ Icc (-halfWidth) halfWidth := by
        intro h
        have : |x| ≤ halfWidth := abs_le.mpr h
        linarith
      unfold indicator
      rw [if_neg h_not]
      have hb0 := basis_eq_zero_of_not_mem n x h_gt
      rw [hb0, zero_mul]
  rw [integral_congr_ae h_ae]
  exact integral_indicator (μ := volume) (measurableSet_Icc : MeasurableSet (Icc (-halfWidth) halfWidth))

lemma integral_low_mul_eq_sum
    (o : Bool) (u : ℝ → ℝ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Icc (-halfWidth) halfWidth))) :
    (∫ x, low o u x * g x) =
      ∑ j : I, alpha o u j * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * g y) := by
  have hi (j : I) : Integrable (fun x => alpha o u j * (basis (degree o j) x * g x)) volume :=
    (integrable_mul_basis_of_restrict_memLp (degree o j) g hg).const_mul _
  have he (x : ℝ) : low o u x * g x =
      ∑ j : I, alpha o u j * (basis (degree o j) x * g x) := by
    dsimp [low]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  congr 1
  exact integral_basis_mul_eq_setIntegral (degree o j) g

lemma polarize_quadratic_integral
    (f h g : ℝ → ℝ)
    (hf : Integrable (fun x => f x * g x) volume)
    (hh : Integrable (fun x => h x * g x) volume) :
    polarize (fun v => 2 * (∫ x, v x * g x)^2) f h =
      2 * (∫ x, f x * g x) * (∫ x, h x * g x) := by
  unfold polarize
  dsimp only
  have he : (fun x => (f x + h x) * g x) = (fun x => f x * g x + h x * g x) := by
    ext x; ring
  rw [he, integral_add hf hh]
  ring

lemma polarize_targetQ_cosh (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    polarize targetQ_cosh (low o u) (tail o u) =
      ∑ j : I, alpha o u j *
        (∫ x, (2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.cosh (y/2)) * Real.cosh (x/2)) * tail o u x) := by
  have hg : MemLp (fun x => Real.cosh (x/2)) 2 (volume.restrict (Icc (-halfWidth) halfWidth)) :=
    cosh_half_memLp halfWidth
  have hi_low : Integrable (fun x => low o u x * Real.cosh (x/2)) volume :=
    integrable_mul_low_of_restrict_memLp o u _ hg
  have hi_tail : Integrable (fun x => Real.cosh (x/2) * tail o u x) volume :=
    integrable_mul_tail_of_restrict_memLp o u hu (fun x => Real.cosh (x/2)) hg
  have hi_tail' : Integrable (fun x => tail o u x * Real.cosh (x/2)) volume := by
    have he : (fun x => tail o u x * Real.cosh (x/2)) = (fun x => Real.cosh (x/2) * tail o u x) := by ext x; ring
    rw [he]; exact hi_tail
  change polarize (fun v => 2 * (∫ x, v x * Real.cosh (x/2))^2) (low o u) (tail o u) = _
  rw [polarize_quadratic_integral _ _ _ hi_low hi_tail']
  rw [integral_low_mul_eq_sum o u _ hg]
  have h_expand : (2 * ∑ j : I, alpha o u j * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.cosh (y/2))) *
      (∫ x, tail o u x * Real.cosh (x/2)) =
      ∑ j : I, 2 * (alpha o u j * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.cosh (y/2))) *
        (∫ x, tail o u x * Real.cosh (x/2)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h_expand]
  apply Finset.sum_congr rfl
  intro j _
  have h_comm (y_int : ℝ) : 2 * (alpha o u j * y_int) * (∫ x, tail o u x * Real.cosh (x/2)) =
      alpha o u j * (2 * y_int * (∫ x, tail o u x * Real.cosh (x/2))) := by ring
  rw [h_comm]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

lemma polarize_targetQ_sinh (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    polarize targetQ_sinh (low o u) (tail o u) =
      ∑ j : I, alpha o u j *
        (∫ x, (2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.sinh (y/2)) * Real.sinh (x/2)) * tail o u x) := by
  have hg : MemLp (fun x => Real.sinh (x/2)) 2 (volume.restrict (Icc (-halfWidth) halfWidth)) :=
    sinh_half_memLp halfWidth
  have hi_low : Integrable (fun x => low o u x * Real.sinh (x/2)) volume :=
    integrable_mul_low_of_restrict_memLp o u _ hg
  have hi_tail : Integrable (fun x => Real.sinh (x/2) * tail o u x) volume :=
    integrable_mul_tail_of_restrict_memLp o u hu (fun x => Real.sinh (x/2)) hg
  have hi_tail' : Integrable (fun x => tail o u x * Real.sinh (x/2)) volume := by
    have he : (fun x => tail o u x * Real.sinh (x/2)) = (fun x => Real.sinh (x/2) * tail o u x) := by ext x; ring
    rw [he]; exact hi_tail
  change polarize (fun v => 2 * (∫ x, v x * Real.sinh (x/2))^2) (low o u) (tail o u) = _
  rw [polarize_quadratic_integral _ _ _ hi_low hi_tail']
  rw [integral_low_mul_eq_sum o u _ hg]
  have h_expand : (2 * ∑ j : I, alpha o u j * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.sinh (y/2))) *
      (∫ x, tail o u x * Real.sinh (x/2)) =
      ∑ j : I, 2 * (alpha o u j * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.sinh (y/2))) *
        (∫ x, tail o u x * Real.sinh (x/2)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h_expand]
  apply Finset.sum_congr rfl
  intro j _
  have h_comm (y_int : ℝ) : 2 * (alpha o u j * y_int) * (∫ x, tail o u x * Real.sinh (x/2)) =
      alpha o u j * (2 * y_int * (∫ x, tail o u x * Real.sinh (x/2))) := by ring
  rw [h_comm]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The pole polarization identity holds unconditionally. -/
theorem g2_polarization_pole_unconditional : G2PolarizationPole := by
  intro o u hu
  rw [polarize_targetQ_cosh o u hu, polarize_targetQ_sinh o u hu]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub]
  congr 1
  have hi_cosh : Integrable (fun x =>
      (2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.cosh (y/2)) * Real.cosh (x/2)) * tail o u x) volume := by
    apply integrable_mul_tail_of_restrict_memLp o u hu
    exact term4_memLp halfWidth (basisPoly (degree o j))
  have hi_sinh : Integrable (fun x =>
      (2 * (∫ y in Icc (-halfWidth) halfWidth, (basisPoly (degree o j)).eval y * Real.sinh (y/2)) * Real.sinh (x/2)) * tail o u x) volume := by
    apply integrable_mul_tail_of_restrict_memLp o u hu
    exact term5_memLp halfWidth (basisPoly (degree o j))
  rw [← integral_sub hi_cosh hi_sinh]
  congr 1
  ext x
  unfold col_pole
  ring

lemma integral_mul_shift_eq (f g : ℝ → ℝ) (s : ℝ) :
    (∫ x, g x * f (x - s)) = ∫ x, f x * g (x + s) := by
  have h := (MeasureTheory.integral_add_right_eq_self (μ := volume) (fun x => g x * f (x - s)) s).symm
  rw [h]
  congr 1
  ext x
  have : x + s - s = x := by ring
  rw [this]
  ring

lemma polarize_comm (F : (ℝ → ℝ) → ℝ) (f g : ℝ → ℝ) :
    polarize F f g = polarize F g f := by
  unfold polarize
  have : (fun x => f x + g x) = (fun x => g x + f x) := by ext x; ring
  rw [this]
  ring

lemma polarize_real_autocorr (f g : ℝ → ℝ) (s : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    polarize (fun u => real_autocorr u s) f g =
      ( (∫ x, f x * g (x - s)) + (∫ x, g x * f (x - s)) ) / 2 := by
  have hf_shift : MemLp (fun x => f (x - s)) 2 volume := memLp_comp_sub_right f s hf
  have hg_shift : MemLp (fun x => g (x - s)) 2 volume := memLp_comp_sub_right g s hg
  have h_ff : Integrable (fun x => f x * f (x - s)) volume := hf.integrable_mul hf_shift
  have h_fg : Integrable (fun x => f x * g (x - s)) volume := hf.integrable_mul hg_shift
  have h_gf : Integrable (fun x => g x * f (x - s)) volume := hg.integrable_mul hf_shift
  have h_gg : Integrable (fun x => g x * g (x - s)) volume := hg.integrable_mul hg_shift
  have h_sum1 : Integrable (fun x => f x * f (x - s) + f x * g (x - s)) volume := h_ff.add h_fg
  have h_sum2 : Integrable (fun x => g x * f (x - s) + g x * g (x - s)) volume := h_gf.add h_gg
  have h_sum_all : Integrable (fun x => (f x * f (x - s) + f x * g (x - s)) + (g x * f (x - s) + g x * g (x - s))) volume :=
    h_sum1.add h_sum2
  unfold polarize real_autocorr
  dsimp only
  have he : (fun x => (f x + g x) * (f (x - s) + g (x - s))) =
      (fun x => (f x * f (x - s) + f x * g (x - s)) + (g x * f (x - s) + g x * g (x - s))) := by
    ext x; ring
  rw [he]
  rw [integral_add h_sum1 h_sum2]
  rw [integral_add h_ff h_fg]
  rw [integral_add h_gf h_gg]
  ring

lemma polarize_real_autocorr_symm (f g : ℝ → ℝ) (s : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    polarize (fun u => real_autocorr u s) f g =
      ( (∫ x, f x * g (x - s)) + (∫ x, f x * g (x + s)) ) / 2 := by
  rw [polarize_real_autocorr f g s hf hg]
  rw [integral_mul_shift_eq f g s]

lemma polarize_targetQ_prime_single (o : Bool) (u : ℝ → ℝ) (hu : Test u) (s : ℝ) :
    2 * polarize (fun v => real_autocorr v s) (low o u) (tail o u) =
      (∫ x, tail o u x * low o u (x - s)) + (∫ x, tail o u x * low o u (x + s)) := by
  rw [polarize_comm]
  rw [polarize_real_autocorr_symm (tail o u) (low o u) s (tail_memLp o u hu) (low_memLp o u)]
  ring

lemma polarize_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → (ℝ → ℝ) → ℝ) (f g : ℝ → ℝ) :
    polarize (fun u => 2 * ∑ i ∈ s, c i * F i u) f g =
      ∑ i ∈ s, c i * (2 * polarize (F i) f g) := by
  unfold polarize
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma prime_pointwise_sum_eq (o : Bool) (u : ℝ → ℝ) (x : ℝ) :
    (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) =
    ∑ j : I, alpha o u j * (col_prime halfWidth (basisPoly (degree o j)) x * tail o u x) := by
  have h_low (s : ℝ) : low o u s = ∑ j : I, alpha o u j * zeroPoly halfWidth (basisPoly (degree o j)) s := rfl
  simp_rw [h_low]
  have h_step1 (n : ℕ) :
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ((∑ j : I, alpha o u j * zeroPoly halfWidth (basisPoly (degree o j)) (x - Real.log n)) +
         (∑ j : I, alpha o u j * zeroPoly halfWidth (basisPoly (degree o j)) (x + Real.log n))) * tail o u x =
      ∑ j : I, alpha o u j * (((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (zeroPoly halfWidth (basisPoly (degree o j)) (x - Real.log n) +
         zeroPoly halfWidth (basisPoly (degree o j)) (x + Real.log n)) * tail o u x) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h_step1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  congr 1
  unfold col_prime
  rw [Finset.sum_mul]

lemma tail_mul_low_shift_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (s : ℝ) :
    Integrable (fun x => tail o u x * low o u (x - s)) volume :=
  (tail_memLp o u hu).integrable_mul (memLp_comp_sub_right (low o u) s (low_memLp o u))

lemma tail_mul_low_shift_add_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (s : ℝ) :
    Integrable (fun x => tail o u x * low o u (x + s)) volume :=
  (tail_memLp o u hu).integrable_mul (memLp_comp_add_right (low o u) s (low_memLp o u))

lemma prime_single_term_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) (n : ℕ) :
    Integrable (fun x => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) volume := by
  have h1 := tail_mul_low_shift_integrable o u hu (Real.log n)
  have h2 := tail_mul_low_shift_add_integrable o u hu (Real.log n)
  have he : (fun x => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) =
      (fun x => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (tail o u x * low o u (x - Real.log n)) +
                ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (tail o u x * low o u (x + Real.log n))) := by
    ext x; ring
  rw [he]
  exact (h1.const_mul _).add (h2.const_mul _)

/-- The prime polarization identity holds unconditionally. -/
theorem g2_polarization_prime_unconditional : G2PolarizationPrime := by
  intro o u hu
  change polarize (fun u => 2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    real_autocorr u (Real.log n)) (low o u) (tail o u) = _
  rw [polarize_finsetSum]
  have h_int_single (n : ℕ) :
      2 * polarize (fun v => real_autocorr v (Real.log n)) (low o u) (tail o u) =
        ∫ x, (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x := by
    rw [polarize_targetQ_prime_single o u hu (Real.log n)]
    have h1 := tail_mul_low_shift_integrable o u hu (Real.log n)
    have h2 := tail_mul_low_shift_add_integrable o u hu (Real.log n)
    have he : (fun x => (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) =
        (fun x => tail o u x * low o u (x - Real.log n) + tail o u x * low o u (x + Real.log n)) := by
      ext x; ring
    rw [he, integral_add h1 h2]
  simp_rw [h_int_single]
  have h_in (n : ℕ) :
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (∫ x, (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) =
      ∫ x, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x := by
    rw [← integral_const_mul]
    congr 1; ext x; ring
  simp_rw [h_in]
  rw [← integral_finsetSum _ (fun n _ => prime_single_term_integrable o u hu n)]
  have h_pt := prime_pointwise_sum_eq o u
  have he_pt : (fun x => ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      (low o u (x - Real.log n) + low o u (x + Real.log n)) * tail o u x) =
      (fun x => ∑ j : I, alpha o u j * (col_prime halfWidth (basisPoly (degree o j)) x * tail o u x)) := by
    ext x; exact h_pt x
  rw [he_pt]
  rw [integral_finsetSum _ (fun j _ => (col_prime_mul_tail_integrable o u hu j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]

lemma low_eval_eq_sum (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : x ∈ Icc (-halfWidth) halfWidth) :
    low o u x = ∑ j : I, alpha o u j * (basisPoly (degree o j)).eval x := by
  have h (j : I) : zeroPoly halfWidth (basisPoly (degree o j)) x = (basisPoly (degree o j)).eval x := by
    unfold zeroPoly indicator
    simp [hx]
  change low o u x = _
  unfold low basis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact h j

lemma low_sub_low_eq_sum (o : Bool) (u : ℝ → ℝ) (x y : ℝ)
    (hx : x ∈ Icc (-halfWidth) halfWidth) (hy : y ∈ Icc (-halfWidth) halfWidth) :
    low o u x - low o u y =
      ∑ j : I, alpha o u j * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y) := by
  rw [low_eval_eq_sum o u x hx, low_eval_eq_sum o u y hy]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def arch_column_density (o : Bool) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
    RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) +
  (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x

lemma sum_col_arch_eq_density (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : |x| < halfWidth) :
    (∑ j : I, alpha o u j * col_arch halfWidth (basisPoly (degree o j)) x) =
      arch_column_density o u x := by
  have hx_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt hx)
  have h_low_x : low o u x = ∑ j : I, alpha o u j * (basisPoly (degree o j)).eval x := low_eval_eq_sum o u x hx_icc
  unfold col_arch arch_column_density
  have h_expand (j : I) :
      alpha o u j * ((1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y)) +
      (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (basisPoly (degree o j)).eval x) =
      (1/2:ℝ) * (alpha o u j * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y))) +
      (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (alpha o u j * (basisPoly (degree o j)).eval x) := by
    ring
  simp_rw [h_expand]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  · congr 1
    have h_in (j : I) : alpha o u j * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y)) =
        ∫ y in Icc (-halfWidth) halfWidth,
          alpha o u j * (RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y)) := by
      rw [integral_const_mul]
    simp_rw [h_in]
    rw [← integral_finsetSum]
    · apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      have heq : (∑ i : I, alpha o u i * (RH_GammaFinalFormula.K_kernel |x - y| *
          (Polynomial.eval x (basisPoly (degree o ↑i)) - Polynomial.eval y (basisPoly (degree o ↑i))))) =
          RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) := by
        rw [low_sub_low_eq_sum o u x y hx_icc hy]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      exact heq
    · intro j _
      have hi := kernel_eval_sub_integrableOn halfWidth halfWidth_pos.le (basisPoly (degree o j)) x hx_icc
      have heq : (fun y => alpha o u j * (RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y))) =
          (fun y => alpha o u j • (RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y))) := by
        ext y; rfl
      rw [heq]
      exact hi.smul (alpha o u j)
  · congr 1
    exact h_low_x.symm

lemma sum_col_arch_integral (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∑ j : I, alpha o u j * (∫ x, col_arch halfWidth (basisPoly (degree o j)) x * tail o u x)) =
      ∫ x, (∑ j : I, alpha o u j * col_arch halfWidth (basisPoly (degree o j)) x) * tail o u x := by
  have hi (j : I) : Integrable (fun x => alpha o u j * (col_arch halfWidth (basisPoly (degree o j)) x * tail o u x)) volume :=
    (col_arch_mul_tail_integrable o u hu j).const_mul _
  have h_in (j : I) : alpha o u j * (∫ x, col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) =
      ∫ x, alpha o u j * (col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) := by
    rw [integral_const_mul]
  simp_rw [h_in]
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  congr 1; ext x
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_col_arch_mul_tail_integral (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∑ j : I, alpha o u j * (∫ x, col_arch halfWidth (basisPoly (degree o j)) x * tail o u x)) =
      ∫ x, arch_column_density o u x * tail o u x := by
  rw [sum_col_arch_integral o u hu]
  apply integral_congr_ae
  filter_upwards [ae_abs_ne halfWidth] with x hx
  by_cases h_lt : |x| < halfWidth
  · rw [sum_col_arch_eq_density o u x h_lt]
  · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
    have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
    rw [ht0, mul_zero, mul_zero]

lemma arch_density_mul_tail_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Integrable (fun x => arch_column_density o u x * tail o u x) volume := by
  have h_eq : (fun x => arch_column_density o u x * tail o u x) =ᵐ[volume]
      (fun x => (∑ j : I, alpha o u j * col_arch halfWidth (basisPoly (degree o j)) x) * tail o u x) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · rw [sum_col_arch_eq_density o u x h_lt]
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
      rw [ht0, mul_zero, mul_zero]
  have hi_sum : Integrable (fun x => (∑ j : I, alpha o u j * col_arch halfWidth (basisPoly (degree o j)) x) * tail o u x) volume := by
    have he : (fun x => (∑ j : I, alpha o u j * col_arch halfWidth (basisPoly (degree o j)) x) * tail o u x) =
        (fun x => ∑ j : I, alpha o u j * (col_arch halfWidth (basisPoly (degree o j)) x * tail o u x)) := by
      ext x
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    apply integrable_finsetSum
    intro j _
    exact (col_arch_mul_tail_integrable o u hu j).const_mul _
  exact hi_sum.congr h_eq.symm

lemma tail_term_sum_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (fun x => (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x) =ᵐ[volume]
    (fun x => ∑ j : I, alpha o u j * ((1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (basisPoly (degree o j)).eval x * tail o u x)) := by
  filter_upwards [ae_abs_ne halfWidth] with x hx
  by_cases h_lt : |x| < halfWidth
  · have hx_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt h_lt)
    have h_low : low o u x = ∑ j : I, alpha o u j * (basisPoly (degree o j)).eval x := low_eval_eq_sum o u x hx_icc
    rw [h_low]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
    have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
    rw [ht0]
    simp only [mul_zero]
    exact Finset.sum_const_zero.symm

lemma tail_term_sum_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Integrable (fun x => (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x) volume := by
  have hi_sum : Integrable (fun x => ∑ j : I, alpha o u j * ((1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (basisPoly (degree o j)).eval x * tail o u x)) volume := by
    apply integrable_finsetSum
    intro j _
    exact (tail_term_mul_tail_integrable o u hu j).const_mul _
  exact hi_sum.congr (tail_term_sum_ae_eq o u hu).symm

lemma kernel_term_sum_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x) =ᵐ[volume]
    (fun x => arch_column_density o u x * tail o u x - (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x) := by
  filter_upwards [ae_abs_ne halfWidth] with x hx
  by_cases h_lt : |x| < halfWidth
  · unfold arch_column_density
    ring
  · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
    have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
    rw [ht0]
    ring

lemma kernel_term_sum_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Integrable (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x) volume := by
  have hi_diff : Integrable (fun x => arch_column_density o u x * tail o u x - (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x) volume :=
    (arch_density_mul_tail_integrable o u hu).sub (tail_term_sum_integrable o u hu)
  exact hi_diff.congr (kernel_term_sum_ae_eq o u hu).symm

lemma density_integral_decompose (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∫ x, arch_column_density o u x * tail o u x) =
    (∫ x, (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x) +
    (∫ x, (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x) := by
  have h_add : (fun x => arch_column_density o u x * tail o u x) =ᵐ[volume]
      (fun x => ((1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x) +
        ((1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x)) := by
    filter_upwards [ae_abs_ne halfWidth] with x hx
    by_cases h_lt : |x| < halfWidth
    · unfold arch_column_density
      ring
    · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
      have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
      rw [ht0]
      ring
  rw [integral_congr_ae h_add]
  exact integral_add (kernel_term_sum_integrable o u hu) (tail_term_sum_integrable o u hu)

lemma outside_tail_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y))) =
    (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x := by
  have h_ae : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y)))
      (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x * tail o u x)) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs, tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl h_ae]
  rw [integral_mul_const]
  have h_out := (outside_integral hx).2
  change (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, RH_Rebaseline.K_kernel |x-y|) * (low o u x * tail o u x) = _
  rw [h_out]
  ring

lemma outside_integrand_zero_of_abs_gt (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| > halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y))) = 0 := by
  have h_ae : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y)))
      (fun _ => 0) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u x hx, low_eq_zero_of_not_mem o u y h_abs,
        tail_eq_zero_of_not_mem o u hu x hx, tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl h_ae]
  simp only [integral_zero]

lemma arch_density_tail_pointwise (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    arch_column_density o u x * tail o u x =
      (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x +
      (1/2:ℝ) * (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
        RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y))) := by
  unfold arch_column_density
  rw [outside_tail_eq o u hu x hx]
  ring

lemma arch_density_mul_tail_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (fun x => arch_column_density o u x * tail o u x) =ᵐ[volume]
    (fun x => (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x +
      (1/2:ℝ) * (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
        RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y)))) := by
  filter_upwards [ae_abs_ne halfWidth] with x hx
  by_cases h_lt : |x| < halfWidth
  · exact arch_density_tail_pointwise o u hu x h_lt
  · have h_gt : |x| > halfWidth := lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm hx)
    have ht0 := tail_eq_zero_of_not_mem o u hu x h_gt
    have hout := outside_integrand_zero_of_abs_gt o u hu x h_gt
    rw [hout, ht0]
    ring

lemma arch_density_integral_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (∫ x, arch_column_density o u x * tail o u x) =
    (∫ x, ((1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
        RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) * tail o u x +
      (1/2:ℝ) * (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
        RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y))))) :=
  integral_congr_ae (arch_density_mul_tail_ae_eq o u hu)

/-- Pointwise algebraic identity for polarization of quadratic differences. -/
lemma polarize_spatial_diff (f g : ℝ → ℝ) (x y : ℝ) :
    ((f x + g x) - (f y + g y))^2 - (f x - f y)^2 - (g x - g y)^2 =
    2 * (f x - f y) * (g x - g y) := by
  ring

/-- Symmetry of the spatial difference kernel under coordinate swap (x, y) ↔ (y, x). -/
lemma spatial_diff_kernel_symm (o : Bool) (u : ℝ → ℝ) (x y : ℝ) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) =
    RH_GammaFinalFormula.K_kernel |y - x| * (low o u y - low o u x) * (tail o u y - tail o u x) := by
  have h_abs : |x - y| = |y - x| := abs_sub_comm x y
  rw [h_abs]
  ring

/-- The spatial kernel integrand vanishes identically when both variables lie outside the support. -/
lemma spatial_diff_kernel_zero_of_both_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x y : ℝ)
    (hx : |x| > halfWidth) (hy : |y| > halfWidth) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) = 0 := by
  rw [low_eq_zero_of_not_mem o u x hx, low_eq_zero_of_not_mem o u y hy,
      tail_eq_zero_of_not_mem o u hu x hx, tail_eq_zero_of_not_mem o u hu y hy]
  ring

/-- When y lies outside the support, the kernel integrand reduces to K(|x-y|) * low(x) * tail(x). -/
lemma spatial_diff_kernel_outside_y (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x y : ℝ)
    (hy : |y| > halfWidth) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) =
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x * tail o u x) := by
  rw [low_eq_zero_of_not_mem o u y hy, tail_eq_zero_of_not_mem o u hu y hy]
  ring

/-- Inside the support rectangle I × I, the integrand splits into two asymmetric terms. -/
lemma spatial_diff_kernel_inside_expand (o : Bool) (u : ℝ → ℝ) (x y : ℝ) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) =
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * tail o u x -
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * tail o u y := by
  ring

lemma kernel_low_sub_integrableOn (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : x ∈ Icc (-halfWidth) halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)) (Icc (-halfWidth) halfWidth) volume := by
  have heq : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y))
      (fun y => ∑ i : I, alpha o u i * (RH_GammaFinalFormula.K_kernel |x - y| *
        (Polynomial.eval x (basisPoly (degree o ↑i)) - Polynomial.eval y (basisPoly (degree o ↑i)))))
      (Icc (-halfWidth) halfWidth) := by
    intro y hy
    dsimp only
    rw [low_sub_low_eq_sum o u x y hx hy]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply (IntegrableOn.congr_fun _ heq.symm measurableSet_Icc)
  apply integrable_finsetSum
  intro j _
  have hi := kernel_eval_sub_integrableOn halfWidth halfWidth_pos.le (basisPoly (degree o j)) x hx
  have he : (fun y => alpha o u j * (RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y))) =
      (fun y => alpha o u j • (RH_GammaFinalFormula.K_kernel |x-y| * ((basisPoly (degree o j)).eval x - (basisPoly (degree o j)).eval y))) := by
    ext y; rfl
  rw [he]
  exact hi.smul (alpha o u j)

/-- The interior difference kernel decomposes as the sum of a term and its coordinate-swapped reflection. -/
lemma spatial_diff_kernel_eq_add_swap (o : Bool) (u : ℝ → ℝ) (x y : ℝ) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) =
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * tail o u x +
    RH_GammaFinalFormula.K_kernel |y - x| * (low o u y - low o u x) * tail o u y := by
  have h_abs : |y - x| = |x - y| := abs_sub_comm y x
  rw [h_abs]
  ring

/-- Kernel-weighted difference quadratic polarization identity for any test functions. -/
lemma spatial_integrand_add (f g : ℝ → ℝ) (x y : ℝ) :
    RH_GammaFinalFormula.K_kernel |x - y| * ((f x + g x) - (f y + g y))^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (f x - f y)^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (g x - g y)^2 =
    2 * (RH_GammaFinalFormula.K_kernel |x - y| * (f x - f y) * (g x - g y)) := by
  have := polarize_spatial_diff f g x y
  linear_combination RH_GammaFinalFormula.K_kernel |x - y| * this

/-- Quadrant 1: Both variables outside the support [-L, L] -> integrand vanishes identically. -/
lemma quadrant_outside_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x y : ℝ)
    (hx : |x| > halfWidth) (hy : |y| > halfWidth) :
    RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2 = 0 := by
  rw [spatial_integrand_add (low o u) (tail o u) x y]
  rw [spatial_diff_kernel_zero_of_both_outside o u hu x y hx hy]
  ring

/-- Quadrant 2: y outside the support [-L, L] -> integrand reduces to 2 K(|x-y|) low(x) tail(x). -/
lemma quadrant_inside_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x y : ℝ)
    (hy : |y| > halfWidth) :
    RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2 =
    2 * (RH_GammaFinalFormula.K_kernel |x - y| * (low o u x * tail o u x)) := by
  rw [spatial_integrand_add (low o u) (tail o u) x y]
  rw [spatial_diff_kernel_outside_y o u hu x y hy]

/-- Quadrant 3: x outside the support [-L, L] -> integrand reduces to 2 K(|x-y|) low(y) tail(y). -/
lemma quadrant_outside_inside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x y : ℝ)
    (hx : |x| > halfWidth) :
    RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
    RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2 =
    2 * (RH_GammaFinalFormula.K_kernel |x - y| * (low o u y * tail o u y)) := by
  rw [spatial_integrand_add (low o u) (tail o u) x y]
  have h_low_x : low o u x = 0 := low_eq_zero_of_not_mem o u x hx
  have h_tail_x : tail o u x = 0 := tail_eq_zero_of_not_mem o u hu x hx
  rw [h_low_x, h_tail_x]
  ring

/-- Symmetry of outside integral: if y lies inside support, integral over x in I^c gives the tail kernel. -/
lemma outside_tail_eq_swap (o : Bool) (u : ℝ → ℝ) (_hu : Test u) (y : ℝ) (hy : |y| < halfWidth) :
    (∫ x in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (low o u y * tail o u y)) =
    (RH_Rebaseline.T_tail (halfWidth-y) + RH_Rebaseline.T_tail (halfWidth+y)) * low o u y * tail o u y := by
  have h_abs (x : ℝ) : |x - y| = |y - x| := abs_sub_comm x y
  have heq : EqOn (fun x => RH_GammaFinalFormula.K_kernel |x - y| * (low o u y * tail o u y))
      (fun x => (RH_Rebaseline.K_kernel |y - x|) * (low o u y * tail o u y)) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro x _
    dsimp only
    rw [h_abs x]
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc.compl heq]
  rw [integral_mul_const]
  have h_out := (outside_integral hy).2
  rw [h_out]
  ring

/-- Outer integral evaluation for quadrant 3 (x outside): integral over x in I^c evaluates to 2 T_tail * low(y) * tail(y). -/
lemma outside_polarize_eval_eq_swap (o : Bool) (u : ℝ → ℝ) (hu : Test u) (y : ℝ) (hy : |y| < halfWidth) :
    (∫ x in (Icc (-halfWidth) halfWidth)ᶜ,
      (RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
       RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
       RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2)) =
    2 * (RH_Rebaseline.T_tail (halfWidth - y) + RH_Rebaseline.T_tail (halfWidth + y)) * low o u y * tail o u y := by
  have heq : EqOn (fun x =>
      RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
      RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
      RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2)
      (fun x => 2 * (RH_GammaFinalFormula.K_kernel |x - y| * (low o u y * tail o u y)))
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro x hx
    have h_abs : |x| > halfWidth := by
      by_contra h_le
      have : |x| ≤ halfWidth := not_lt.mp h_le
      have : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hx this
    exact quadrant_outside_inside o u hu x y h_abs
  rw [setIntegral_congr_fun measurableSet_Icc.compl heq]
  rw [integral_const_mul]
  rw [outside_tail_eq_swap o u hu y hy]
  ring

/-- Gluing lemma: a function integrable on the support I and on its complement I^c is globally integrable on ℝ. -/
lemma integrable_of_inside_and_outside (f : ℝ → ℝ)
    (h_in : IntegrableOn f (Icc (-halfWidth) halfWidth) volume)
    (h_out : IntegrableOn f (Icc (-halfWidth) halfWidth)ᶜ volume) :
    Integrable f volume := by
  have hu : (Icc (-halfWidth) halfWidth) ∪ (Icc (-halfWidth) halfWidth)ᶜ = univ := union_compl_self _
  have h_univ : IntegrableOn f univ volume := hu ▸ (h_in.union h_out)
  exact integrableOn_univ.mp h_univ

/-- Domain decomposition of real Bochner integrals into support I and outside I^c. -/
lemma integral_split_inside_outside (f : ℝ → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = (∫ x in Icc (-halfWidth) halfWidth, f x) + (∫ x in (Icc (-halfWidth) halfWidth)ᶜ, f x) := by
  rw [← integral_add_compl measurableSet_Icc hf]

/-- The unified pointwise polarized Archimedean difference integrand. -/
noncomputable def polarize_integrand (o : Bool) (u : ℝ → ℝ) (x y : ℝ) : ℝ :=
  RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2 -
  RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2 -
  RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2

/-- Pointwise algebraic identity relating the cross difference kernel to half of polarize_integrand. -/
lemma cross_diff_eq_half_polarize (o : Bool) (u : ℝ → ℝ) (x y : ℝ) :
    RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y) =
    (1/2:ℝ) * polarize_integrand o u x y := by
  unfold polarize_integrand
  have := spatial_integrand_add (low o u) (tail o u) x y
  linarith

/-- Direct single-integral outside evaluation for quadrant 2 (y outside):
    integral of polarize_integrand over y in I^c evaluates to 2 T_tail * low(x) * tail(x). -/
lemma polarize_integrand_outside_y (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, polarize_integrand o u x y) =
    2 * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x := by
  have heq : EqOn (fun y => polarize_integrand o u x y)
      (fun y => (2 * (low o u x * tail o u x)) * (RH_Rebaseline.K_kernel |x - y|))
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    unfold polarize_integrand
    dsimp only
    rw [quadrant_inside_outside o u hu x y h_abs]
    have hk : RH_GammaFinalFormula.K_kernel |x - y| = RH_Rebaseline.K_kernel |x - y| := rfl
    rw [hk]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl heq]
  rw [integral_const_mul]
  have h_out := (outside_integral hx).2
  rw [h_out]
  ring

/-- Direct single-integral outside evaluation for quadrant 1 (both outside):
    integral of polarize_integrand over y in I^c vanishes when x is outside I. -/
lemma polarize_integrand_outside_outside_integral (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| > halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, polarize_integrand o u x y) = 0 := by
  have heq : EqOn (fun y => polarize_integrand o u x y) (fun _ => 0) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    unfold polarize_integrand
    exact quadrant_outside_outside o u hu x y hx h_abs
  rw [setIntegral_congr_fun measurableSet_Icc.compl heq]
  simp only [integral_zero]

/-- Decomposition of the real inner integral when x lies outside the support:
    the outside integral vanishes, leaving only the integral over the support. -/
lemma inner_integral_outside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| > halfWidth)
    (h_int : Integrable (fun y => polarize_integrand o u x y) volume) :
    (∫ y, polarize_integrand o u x y) =
    (∫ y in Icc (-halfWidth) halfWidth, polarize_integrand o u x y) := by
  rw [integral_split_inside_outside (fun y => polarize_integrand o u x y) h_int]
  rw [polarize_integrand_outside_outside_integral o u hu x hx]
  ring

/-- Decomposition of the real inner integral when x lies inside the support:
    splits into the integral over the support plus the tail kernel evaluation. -/
lemma inner_integral_inside (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth)
    (h_int : Integrable (fun y => polarize_integrand o u x y) volume) :
    (∫ y, polarize_integrand o u x y) =
    (∫ y in Icc (-halfWidth) halfWidth, polarize_integrand o u x y) +
    2 * (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) * low o u x * tail o u x := by
  rw [integral_split_inside_outside (fun y => polarize_integrand o u x y) h_int]
  rw [polarize_integrand_outside_y o u hu x hx]

lemma outside_low_sq_eq (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)^2) =
    (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (low o u x)^2 := by
  have h_ae : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)^2)
      (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x)^2) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl h_ae]
  rw [integral_mul_const]
  have h_out := (outside_integral hx).2
  change (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, RH_Rebaseline.K_kernel |x-y|) * (low o u x)^2 = _
  rw [h_out]

lemma outside_tail_sq_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x - tail o u y)^2) =
    (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (tail o u x)^2 := by
  have h_ae : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x - tail o u y)^2)
      (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x)^2) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl h_ae]
  rw [integral_mul_const]
  have h_out := (outside_integral hx).2
  change (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, RH_Rebaseline.K_kernel |x-y|) * (tail o u x)^2 = _
  rw [h_out]

lemma outside_low_add_tail_sq_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2) =
    (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * (low o u x + tail o u x)^2 := by
  have h_ae : EqOn (fun y => RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2)
      (fun y => RH_GammaFinalFormula.K_kernel |x-y| * (low o u x + tail o u x)^2) (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs, tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc.compl h_ae]
  rw [integral_mul_const]
  have h_out := (outside_integral hx).2
  change (∫ y in (Icc (-halfWidth) halfWidth)ᶜ, RH_Rebaseline.K_kernel |x-y|) * (low o u x + tail o u x)^2 = _
  rw [h_out]

lemma outside_polarize_pointwise (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2) -
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)^2) -
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x - tail o u y)^2) =
    2 * (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x - low o u y) * (tail o u x - tail o u y))) := by
  rw [outside_low_add_tail_sq_eq o u hu x hx,
      outside_low_sq_eq o u x hx,
      outside_tail_sq_eq o u hu x hx,
      outside_tail_eq o u hu x hx]
  ring

lemma outside_polarize_eval_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2) -
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (low o u x - low o u y)^2) -
    (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
      RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x - tail o u y)^2) =
    2 * (RH_Rebaseline.T_tail (halfWidth-x) + RH_Rebaseline.T_tail (halfWidth+x)) * low o u x * tail o u x := by
  rw [outside_polarize_pointwise o u hu x hx]
  rw [outside_tail_eq o u hu x hx]
  ring

lemma integrableOn_outside_kernel_tail (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y))
      (Icc (-halfWidth) halfWidth)ᶜ volume := by
  have h_ae : EqOn (fun y => (low o u x * tail o u x) * RH_GammaFinalFormula.K_kernel |x - y|)
      (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y))
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs, tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  have hi_k : IntegrableOn (fun y => RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    (outside_integral hx).1
  have hi_const : IntegrableOn (fun y => (low o u x * tail o u x) * RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    hi_k.const_mul (low o u x * tail o u x)
  exact hi_const.congr_fun h_ae measurableSet_Icc.compl

lemma integrableOn_outside_low_sq (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : |x| < halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2)
      (Icc (-halfWidth) halfWidth)ᶜ volume := by
  have h_ae : EqOn (fun y => ((low o u x)^2) * RH_GammaFinalFormula.K_kernel |x - y|)
      (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y)^2)
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs]
    ring
  have hi_k : IntegrableOn (fun y => RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    (outside_integral hx).1
  have hi_const : IntegrableOn (fun y => ((low o u x)^2) * RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    hi_k.const_mul ((low o u x)^2)
  exact hi_const.congr_fun h_ae measurableSet_Icc.compl

lemma integrableOn_outside_tail_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2)
      (Icc (-halfWidth) halfWidth)ᶜ volume := by
  have h_ae : EqOn (fun y => ((tail o u x)^2) * RH_GammaFinalFormula.K_kernel |x - y|)
      (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (tail o u x - tail o u y)^2)
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  have hi_k : IntegrableOn (fun y => RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    (outside_integral hx).1
  have hi_const : IntegrableOn (fun y => ((tail o u x)^2) * RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    hi_k.const_mul ((tail o u x)^2)
  exact hi_const.congr_fun h_ae measurableSet_Icc.compl

lemma integrableOn_outside_low_add_tail_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| < halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2)
      (Icc (-halfWidth) halfWidth)ᶜ volume := by
  have h_ae : EqOn (fun y => (((low o u x + tail o u x))^2) * RH_GammaFinalFormula.K_kernel |x - y|)
      (fun y => RH_GammaFinalFormula.K_kernel |x - y| * ((low o u x + tail o u x) - (low o u y + tail o u y))^2)
      (Icc (-halfWidth) halfWidth)ᶜ := by
    intro y hy
    dsimp only
    have h_abs : |y| > halfWidth := by
      by_contra h_le
      have : |y| ≤ halfWidth := not_lt.mp h_le
      have : y ∈ Icc (-halfWidth) halfWidth := abs_le.mp this
      exact hy this
    rw [low_eq_zero_of_not_mem o u y h_abs, tail_eq_zero_of_not_mem o u hu y h_abs]
    ring
  have hi_k : IntegrableOn (fun y => RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    (outside_integral hx).1
  have hi_const : IntegrableOn (fun y => (((low o u x + tail o u x))^2) * RH_Rebaseline.K_kernel |x - y|) (Icc (-halfWidth) halfWidth)ᶜ volume :=
    hi_k.const_mul (((low o u x + tail o u x))^2)
  exact hi_const.congr_fun h_ae measurableSet_Icc.compl

lemma integrableOn_inside_first_term (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : |x| < halfWidth) :
    IntegrableOn (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * tail o u x)
      (Icc (-halfWidth) halfWidth) volume := by
  have hx_icc : x ∈ Icc (-halfWidth) halfWidth := abs_le.mp (le_of_lt hx)
  have hi := kernel_low_sub_integrableOn o u x hx_icc
  have he : (fun y => RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * tail o u x) =
      (fun y => (tail o u x) • (RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y))) := by
    ext y; ring
  rw [he]
  exact hi.smul (tail o u x)


/-- Expansion of the polarized Archimedean kernel energy into iterated difference integrals. -/
lemma polarize_targetQ_energy_expand (f g : ℝ → ℝ) :
    polarize targetQ_energy f g =
    (1/8:ℝ) * ((∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x - y| * ((f x + g x) - (f y + g y))^2) -
               (∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x - y| * (f x - f y)^2) -
               (∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x - y| * (g x - g y)^2)) := by
  unfold polarize targetQ_energy spatialEnergy
  ring

/-- Pure potential-theoretic spatial energy density identity:
    the polarization of the Archimedean kernel energy equals the integral against the spatial column density. -/
def PolarizeSpatialEnergyDensity : Prop := ∀ o u, Test u →
  polarize targetQ_energy (low o u) (tail o u) =
    ∫ x, arch_column_density o u x * tail o u x

/-- Spatial energy polarization form: polarization of the kernel energy equals the cross double integral. -/
def SpatialEnergyPolarization : Prop :=
  ∀ o u, Test u →
    polarize spatialEnergy (low o u) (tail o u) =
      (1/4:ℝ) * ∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y)

/-- Spatial energy density integral: the cross double integral of low and tail equals the column density integral. -/
def SpatialEnergyDensityIntegral : Prop :=
  ∀ o u, Test u →
    (1/4:ℝ) * (∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y)) =
      ∫ x, arch_column_density o u x * tail o u x

/-- Master synthesis of PolarizeSpatialEnergyDensity from its two fundamental components. -/
theorem polarize_spatial_energy_density_of_components
    (h1 : SpatialEnergyPolarization)
    (h2 : SpatialEnergyDensityIntegral) :
    PolarizeSpatialEnergyDensity := by
  intro o u hu
  unfold targetQ_energy
  rw [h1 o u hu, h2 o u hu]

/-- G2PolarizationArch is derived unconditionally from the pure spatial energy density identity. -/
theorem g2_polarization_arch_of_density (h : PolarizeSpatialEnergyDensity) :
    G2PolarizationArch := by
  intro o u hu
  rw [sum_col_arch_mul_tail_integral o u hu]
  exact h o u hu


structure G2PairingPrerequisites : Prop where
  l2 : G2PolarizationL2
  arch : G2PolarizationArch
  pole : G2PolarizationPole
  prime : G2PolarizationPrime
  col_lin : G2ColumnLinearity

structure G2PairingComponents : Prop where
  arch : G2PolarizationArch
  pole : G2PolarizationPole
  prime : G2PolarizationPrime
  col_lin : G2ColumnLinearity

/-- The canonical column pairing identity: the polarization form of low and tail
    equals the alpha-weighted sum of inner products of col and tail. -/
def G2PairingIdentity : Prop := ∀ o u, Test u →
  (targetQ_real (fun x => low o u x + tail o u x) - targetQ_real (low o u) - targetQ_real (tail o u)) / 2 =
    ∑ j : I, alpha o u j * inner ℝ (embed (col o j)) (embed (tail o u))

/-- Master synthesis theorem: G2PairingIdentity is derived from the structured pairing prerequisites. -/
theorem g2_pairing_identity_of_prerequisites (h : G2PairingPrerequisites) : G2PairingIdentity := by
  intro o u hu
  change polarize targetQ_real (low o u) (tail o u) = _
  rw [polarize_targetQ_real]
  rw [h.l2 o u hu, h.arch o u hu, h.pole o u hu, h.prime o u hu]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h_alg : alpha o u j * (∫ (x : ℝ), col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x) +
      alpha o u j * (∫ (x : ℝ), col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) +
      alpha o u j * (∫ (x : ℝ), col_pole halfWidth (basisPoly (degree o j)) x * tail o u x) -
      alpha o u j * (∫ (x : ℝ), col_prime halfWidth (basisPoly (degree o j)) x * tail o u x) =
      alpha o u j * (
        (∫ (x : ℝ), col_L2 halfWidth (basisPoly (degree o j)) x * tail o u x) +
        (∫ (x : ℝ), col_arch halfWidth (basisPoly (degree o j)) x * tail o u x) +
        (∫ (x : ℝ), col_pole halfWidth (basisPoly (degree o j)) x * tail o u x) -
        (∫ (x : ℝ), col_prime halfWidth (basisPoly (degree o j)) x * tail o u x)) := by ring
  rw [h_alg]
  rw [h.col_lin o u hu j]

/-- Synthesis theorem with L^2 polarization unconditionally discharged. -/
theorem g2_pairing_identity_of_components (h : G2PairingComponents) : G2PairingIdentity :=
  g2_pairing_identity_of_prerequisites ⟨g2_polarization_L2_unconditional, h.arch, h.pole, h.prime, h.col_lin⟩

/-- Synthesis theorem with L^2, pole, prime, and column linearity all unconditionally discharged.
    Only the Archimedean energy polarization remains. -/
theorem g2_pairing_identity_of_arch (h_arch : G2PolarizationArch) : G2PairingIdentity :=
  g2_pairing_identity_of_components ⟨h_arch, g2_polarization_pole_unconditional, g2_polarization_prime_unconditional, g2_column_linearity_unconditional⟩

/-- Reduction theorem for G2BilinearRepresentation: if the polarization form of low and tail
    equals the sum of inner products of col and tail, then G2BilinearRepresentation holds. -/
theorem g2_bilinear_representation_of_pairing
    (h : G2PairingIdentity) :
    G2BilinearRepresentation := by
  intro o u hu
  rw [g2_lhs_polarization o u]
  rw [h o u hu]
  rw [g2_rhs_col_tail o u hu]

/-- G2 transfer from the canonical column pairing identity. -/
theorem g2_of_pairing
    (h : G2PairingIdentity) :
    G2 concrete :=
  g2_of_representation (g2_bilinear_representation_of_pairing h)

/-- G2 transfer directly from the pairing components. -/
theorem g2_of_pairing_components (h : G2PairingComponents) : G2 concrete :=
  g2_of_pairing (g2_pairing_identity_of_components h)

/-- G2 transfer directly from the Archimedean energy polarization only. -/
theorem g2_of_arch (h_arch : G2PolarizationArch) : G2 concrete :=
  g2_of_pairing (g2_pairing_identity_of_arch h_arch)

/-- G2 transfer directly from the Archimedean spatial energy density identity. -/
theorem g2_of_density (h_density : PolarizeSpatialEnergyDensity) : G2 concrete :=
  g2_of_arch (g2_polarization_arch_of_density h_density)

/-- G2 pairing identity directly from the Archimedean spatial energy density identity. -/
theorem g2_pairing_identity_of_density (h_density : PolarizeSpatialEnergyDensity) : G2PairingIdentity :=
  g2_pairing_identity_of_arch (g2_polarization_arch_of_density h_density)

/-- G2 transfer directly from the spatial energy components (polarization and density integral). -/
theorem g2_of_spatial_components
    (h1 : SpatialEnergyPolarization)
    (h2 : SpatialEnergyDensityIntegral) : G2 concrete :=
  g2_of_density (polarize_spatial_energy_density_of_components h1 h2)

/-- G2 pairing identity directly from the spatial energy components. -/
theorem g2_pairing_identity_of_spatial_components
    (h1 : SpatialEnergyPolarization)
    (h2 : SpatialEnergyDensityIntegral) : G2PairingIdentity :=
  g2_pairing_identity_of_density (polarize_spatial_energy_density_of_components h1 h2)

end RHStepA2G2







