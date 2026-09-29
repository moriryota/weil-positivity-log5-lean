import PrEncl0511

/-! # 0511: structural row evaluation for the Pr kernel checks

`rowFrom a2 a3 a4 w2 w3 w4 B2 B3 B4` walks the three `B` lists once; its `k`-th entry is
`(Σ_m mulB w_m (dB a_m (B_m[k])), (0,0))`. With `a_m = R_m.1[n]` this is `prT R2 R3 R4 n k`. -/

namespace RHPrRow0511
open RHBall0504 RHBallDot0509 RHPrBall0511 RHPrEncl0511

def rowFrom (a2 a3 a4 : List Ball) (w2 w3 w4 : Ball) :
    List (List Ball) → List (List Ball) → List (List Ball) → List (Ball × Ball)
  | b2 :: B2, b3 :: B3, b4 :: B4 =>
      (add (add (mulB S512 w2 (dB S512 a2 b2)) (mulB S512 w3 (dB S512 a3 b3))) (mulB S512 w4 (dB S512 a4 b4)),
        ((0 : ℤ), (0 : ℕ))) :: rowFrom a2 a3 a4 w2 w3 w4 B2 B3 B4
  | _, _, _ => []

theorem rowFrom_get (a2 a3 a4 : List Ball) (w2 w3 w4 : Ball) :
    ∀ (B2 B3 B4 : List (List Ball)) (k : ℕ), k < B2.length → k < B3.length → k < B4.length →
      (rowFrom a2 a3 a4 w2 w3 w4 B2 B3 B4).getD k ((0,0),(0,0)) =
        (add (add (mulB S512 w2 (dB S512 a2 (B2.getD k []))) (mulB S512 w3 (dB S512 a3 (B3.getD k []))))
          (mulB S512 w4 (dB S512 a4 (B4.getD k []))), ((0 : ℤ), (0 : ℕ)))
  | b2 :: B2, b3 :: B3, b4 :: B4, 0, _, _, _ => by simp [rowFrom]
  | b2 :: B2, b3 :: B3, b4 :: B4, k + 1, h2, h3, h4 => by
      simp only [rowFrom, List.getD_cons_succ]
      exact rowFrom_get a2 a3 a4 w2 w3 w4 B2 B3 B4 k (by simpa using h2) (by simpa using h3) (by simpa using h4)
  | [], _, _, k, h, _, _ => by simp at h
  | _ :: _, [], _, k, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], k, _, _, h => by simp at h

lemma lenB (sB wB : Ball) : (rowB sB wB 64 128).2.1.length = 128 := by
  unfold rowB afAll
  have : ∀ c l b0 b1, (afList S512 (aOf sB) (g2Of sB) c l b0 b1).length = c := by
    intro c; induction c with
    | zero => intro l b0 b1; rfl
    | succ c ih => intro l b0 b1; simp [afList, ih]
  exact this 128 0 _ _

theorem row_eq_prT (n k : ℕ) (hk : k < 128) :
    ((rowFrom (R2.1.getD n []) (R3.1.getD n []) (R4.1.getD n []) R2.2.2 R3.2.2 R4.2.2 R2.2.1 R3.2.1 R4.2.1).getD k
      ((0,0),(0,0))).1 = prT R2 R3 R4 n k := by
  rw [rowFrom_get _ _ _ _ _ _ _ _ _ k (by rw [R2, lenB]; exact hk) (by rw [R3, lenB]; exact hk) (by rw [R4, lenB]; exact hk)]
  rfl

end RHPrRow0511

