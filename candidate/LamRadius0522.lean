import LamCore0522

namespace RHLamRadius0522
open RHBall0504 RHLamDef0521

lemma upper_nat {S : ℕ} (hS : 0 < S) {κ : ℝ} {kB : Ball}
    (hk : mem S κ kB) (h0 : 0 ≤ κ) (hK : kB.1+kB.2 < (S:ℤ)) :
    κ ≤ ((kB.1+kB.2).toNat : ℝ)/S ∧ (kB.1+kB.2).toNat < S := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have hu : κ ≤ ((kB.1:ℝ)+kB.2)/S := by
    have h := (abs_le.mp hk).2
    linarith [show ((kB.1:ℝ)+kB.2)/S = (kB.1:ℝ)/S + kB.2/S by ring]
  have hz : (0:ℝ) ≤ (kB.1:ℝ)+kB.2 := by
    have h := (le_div_iff₀ hS').mp hu
    exact (mul_nonneg h0 hS'.le).trans h
  have hzi : (0:ℤ) ≤ kB.1+kB.2 := by exact_mod_cast hz
  have he : (((kB.1+kB.2).toNat : ℕ):ℤ) = kB.1+kB.2 := Int.toNat_of_nonneg hzi
  have her : ((kB.1+kB.2).toNat : ℝ) = (kB.1:ℝ)+kB.2 := by exact_mod_cast he
  constructor
  · rwa [her]
  · have h := hK
    rw [← he] at h
    exact_mod_cast h

lemma kappa_lt_one {S : ℕ} (hS : 0 < S) {κ : ℝ} {kB : Ball}
    (hk : mem S κ kB) (h0 : 0 ≤ κ) (hK : kB.1+kB.2 < (S:ℤ)) : κ < 1 := by
  obtain ⟨hu,hlt⟩ := upper_nat hS hk h0 hK
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hlt' : ((kB.1+kB.2).toNat:ℝ) < S := by exact_mod_cast hlt
  exact hu.trans_lt ((div_lt_one hs).mpr hlt')

lemma integer_radius (S K R : ℕ) (hS : 0 < S) (hK : K < S) :
    2*((K:ℝ)/S)^(R+1)/(1-(K:ℝ)/S) ≤
      (((2*K^(R+1)*S + S^R*(S-K)-1)/(S^R*(S-K))+1 : ℕ):ℝ)/S := by
  let D : ℕ := S^R*(S-K)
  let N : ℕ := 2*K^(R+1)*S
  have hD : 0 < D := Nat.mul_pos (pow_pos hS R) (Nat.sub_pos_of_lt hK)
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hceil : N ≤ ((N+D-1)/D+1)*D := by
    rw [Nat.add_mul, Nat.one_mul]
    have h := Nat.lt_div_mul_add (a := N+D-1) hD
    omega
  have hr : (N:ℝ) ≤ (((N+D-1)/D+1:ℕ):ℝ)*D := by exact_mod_cast hceil
  have he : 2*((K:ℝ)/S)^(R+1)/(1-(K:ℝ)/S) = (N:ℝ)/D/S := by
    have hk : (K:ℝ) < S := by exact_mod_cast hK
    have hdiff : ((S-K:ℕ):ℝ) = (S:ℝ)-K := Nat.cast_sub hK.le
    dsimp [N,D]
    push_cast
    rw [hdiff]
    rw [pow_succ,div_pow]
    field_simp [hs.ne', (sub_pos.mpr hk).ne']
    <;> ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hs.le
  exact (div_le_iff₀ hd).mpr (by nlinarith [hr])

theorem radius_bound {S : ℕ} (hS : 0 < S) {κ : ℝ} {kB : Ball}
    (hk : mem S κ kB) (h0 : 0 ≤ κ) (hK : kB.1+kB.2 < (S:ℤ)) (R : ℕ) :
    2*κ^(R+1)/(1-κ) ≤ (lamErr S kB R : ℝ)/S := by
  obtain ⟨hu,hlt⟩ := upper_nat hS hk h0 hK
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hlt' : ((kB.1+kB.2).toNat:ℝ)/S < 1 :=
    (div_lt_one hs).mpr (by exact_mod_cast hlt)
  have hp := pow_le_pow_left₀ h0 hu (R+1)
  have hm : 2*κ^(R+1)/(1-κ) ≤ 2*(((kB.1+kB.2).toNat:ℝ)/S)^(R+1)/(1-((kB.1+kB.2).toNat:ℝ)/S) := by
    apply div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  exact hm.trans (integer_radius S _ R hS hlt)

lemma mem_inflate {S E : ℕ} (hS : 0 < S) {x y : ℝ} {b : Ball}
    (hy : mem S y b) (hxy : |x-y| ≤ (E:ℝ)/S) : mem S x (b.1,b.2+E) := by
  unfold mem at *
  simp only [Nat.cast_add]
  rw [add_div]
  exact (abs_sub_le x y ((b.1:ℝ)/S)).trans (by linarith)

end RHLamRadius0522
