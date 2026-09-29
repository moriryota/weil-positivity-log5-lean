import ResidualMembership
import ActualDirections
open MeasureTheory Set
open scoped BigOperators
namespace RHRealLowZero
open RHConditionalLog5 RHLog5Bridge RHRealBasisBridge RHRealCoefficientBridge RHResidualMembership
lemma coeff_basis (m n : ℕ) : coeff (basis m) n = if n=m then 1 else 0 := by
  have h := inner_eq_coeff (basis m) n
    (RHLegendreDirections.direction halfWidth halfWidth_pos.le m) (direction_eq_basis_ae m)
  have ho := (orthonormal_iff_ite.mp (RHLegendreActual.directions_orthonormal halfWidth_pos)) n m
  apply Complex.ofReal_injective
  rw [← h]
  by_cases hnm : n=m <;> simpa [hnm] using ho
lemma coeff_sub (f g : ℝ → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (n : ℕ) :
    coeff (f-g) n = coeff f n - coeff g n := by
  simp only [coeff, Pi.sub_apply, mul_sub]
  exact integral_sub ((basis_memLp n).integrable_mul hf) ((basis_memLp n).integrable_mul hg)
lemma coeff_low (o : Bool) (u : ℝ → ℝ) (k : I) :
    coeff (low o u) (degree o k) = alpha o u k := by
  classical
  have hi (i : I) : Integrable (fun x => alpha o u i * (basis (degree o k) x * basis (degree o i) x)) volume :=
    ((basis_memLp (degree o k)).integrable_mul (basis_memLp (degree o i))).const_mul _
  have he (x : ℝ) : basis (degree o k) x * low o u x =
      ∑ i : I, alpha o u i * (basis (degree o k) x * basis (degree o i) x) := by
    simp only [low, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold coeff
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]
  change (∑ i : I, alpha o u i * coeff (basis (degree o i)) (degree o k)) = _
  have hinj (i : I) : degree o k = degree o i ↔ k=i := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [degree] at h
      omega
    · intro h; rw [h]
  simp [coeff_basis, hinj]
lemma tail_low_zero (o : Bool) (u : ℝ → ℝ) (hu : Test u) (n : ℕ) (hn : n<32) :
    coeff (tail o u) (degree o n) = 0 := by
  let k : I := ⟨n,hn⟩
  change coeff (component o u - low o u) (degree o k) = 0
  rw [coeff_sub _ _ (RHG3RealEmbedding.component_memLp o u hu) (low_memLp o u), coeff_low]
  simp [alpha]
end RHRealLowZero
