import LowBlockB0494
import ConcreteParameters
import Gersh0512

/-! # 0512: `lowForm o (B c)` as an explicit quadratic form, and the reduction of G5c to a row condition

`Mq o p q = Σ_{i,j} B_ip B_jq A0_ij − Σ_i G_ip G_iq / w_i`, `G_ip = Σ_j B_jp At_ij`;
`lowForm o (B *ᵥ c) = Σ_{p,q} c_p c_q Mq o p q`. With the Gershgorin row condition for `μ = 1 − η_o`,
`G5c concrete k` follows. -/

open Finset Matrix
open scoped BigOperators Matrix

namespace RHQForm0512
open RHConditionalLog5 RHLowBlock0494

noncomputable def Bm (o : Bool) : Matrix I I ℝ := RHConcreteParameters.concrete.B o
noncomputable def wt (o : Bool) (i : I) : ℝ := RHConcreteParameters.concrete.weights o i

noncomputable def G (o : Bool) (i p : I) : ℝ := ∑ j : I, Bm o j p * Attrue o i j
noncomputable def Mq (o : Bool) (p q : I) : ℝ :=
  ∑ i : I, ∑ j : I, Bm o i p * Bm o j q * A0true o i j - ∑ i : I, G o i p * G o i q / wt o i

lemma reorder4 (f : I → I → I → I → ℝ) :
    ∑ i : I, ∑ j : I, ∑ p : I, ∑ q : I, f i j p q = ∑ p : I, ∑ q : I, ∑ i : I, ∑ j : I, f i j p q := by
  calc ∑ i : I, ∑ j : I, ∑ p : I, ∑ q : I, f i j p q = ∑ i : I, ∑ p : I, ∑ j : I, ∑ q : I, f i j p q :=
        sum_congr rfl (fun i _ => sum_comm)
    _ = ∑ p : I, ∑ i : I, ∑ j : I, ∑ q : I, f i j p q := sum_comm
    _ = ∑ p : I, ∑ i : I, ∑ q : I, ∑ j : I, f i j p q :=
        sum_congr rfl (fun p _ => sum_congr rfl (fun i _ => sum_comm))
    _ = ∑ p : I, ∑ q : I, ∑ i : I, ∑ j : I, f i j p q := sum_congr rfl (fun p _ => sum_comm)

lemma reorder3 (f : I → I → I → ℝ) :
    ∑ i : I, ∑ p : I, ∑ q : I, f i p q = ∑ p : I, ∑ q : I, ∑ i : I, f i p q := by
  calc ∑ i : I, ∑ p : I, ∑ q : I, f i p q = ∑ p : I, ∑ i : I, ∑ q : I, f i p q := sum_comm
    _ = ∑ p : I, ∑ q : I, ∑ i : I, f i p q := sum_congr rfl (fun p _ => sum_comm)

theorem lowForm_eq (o : Bool) (c : I → ℝ) :
    lowForm o (Bm o *ᵥ c) = ∑ p : I, ∑ q : I, c p * c q * Mq o p q := by
  unfold lowForm Mq
  simp only [mulVec, dotProduct]
  have h1 : ∑ i : I, ∑ j : I, (∑ p : I, Bm o i p * c p) * (∑ q : I, Bm o j q * c q) * A0true o i j =
      ∑ p : I, ∑ q : I, c p * c q * ∑ i : I, ∑ j : I, Bm o i p * Bm o j q * A0true o i j := by
    have e : ∀ i j, (∑ p : I, Bm o i p * c p) * (∑ q : I, Bm o j q * c q) * A0true o i j =
        ∑ p : I, ∑ q : I, c p * c q * (Bm o i p * Bm o j q * A0true o i j) := by
      intro i j; rw [sum_mul_sum, sum_mul]
      exact sum_congr rfl (fun p _ => by rw [sum_mul]; exact sum_congr rfl (fun q _ => by ring))
    simp_rw [e, mul_sum]
    exact reorder4 _
  have h2 : ∀ i : I, (∑ j : I, (∑ p : I, Bm o j p * c p) * Attrue o i j) = ∑ p : I, c p * G o i p := by
    intro i; unfold G
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun p _ => sum_congr rfl (fun j _ => by ring))
  have h3 : ∑ i : I, (∑ j : I, (∑ p : I, Bm o j p * c p) * Attrue o i j) ^ 2 / wt o i =
      ∑ p : I, ∑ q : I, c p * c q * ∑ i : I, G o i p * G o i q / wt o i := by
    have e : ∀ i, (∑ p : I, c p * G o i p) ^ 2 / wt o i = ∑ p : I, ∑ q : I, c p * c q * (G o i p * G o i q / wt o i) := by
      intro i; rw [sq, sum_mul_sum, sum_div]
      exact sum_congr rfl (fun p _ => by rw [sum_div]; exact sum_congr rfl (fun q _ => by ring))
    simp_rw [h2, e, mul_sum]
    exact reorder3 _
  unfold wt Bm at *
  rw [h1, h3, ← sum_sub_distrib]
  refine sum_congr rfl (fun p _ => ?_)
  rw [← sum_sub_distrib]
  exact sum_congr rfl (fun q _ => by ring)

theorem G5c_of_rows (k : RHCaps0494.Caps)
    (h : ∀ (o : Bool) (p : I), 1 - k.eta o ≤ Mq o p p - (1/2) * ∑ q ∈ univ.erase p, (|Mq o p q| + |Mq o q p|)) :
    RHCaps0494.G5c RHConcreteParameters.concrete k := by
  apply G5c_of_lowForm k
  intro o c
  have := RHGersh0512.gersh (Mq o) (1 - k.eta o) (h o) c
  rw [show RHConcreteParameters.concrete.B o = Bm o from rfl, lowForm_eq]
  simpa [sq] using this

end RHQForm0512

