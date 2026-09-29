# 0512: generate T5Tab0512_E.lean / T5Tab0512_O.lean (checked literal stages + row check) from t5mirror.
import t5mirror as tm
def blit(b): return f'({b[0]}, {b[1]})'
def mat(M): return '[' + ',\n  '.join('[' + ', '.join(blit(b) for b in row) + ']' for row in M) + ']'
for o,suf,eta in ((False,'E','1 / 1000'),(True,'O','1 / 1000')):
  st=tm.stages(o); ob='true' if o else 'false'
  dq='odd' if o else 'even'
  L=f'''import EntryBall0512
import BQ0512
import QForm0512

/-! # 0512: T5 stages for parity `{ob}` — checked literal tables and the Gershgorin row check. Candidate only. -/

open Finset
open scoped BigOperators

namespace RHT5{suf}0512
set_option maxRecDepth 1000000
open RHConditionalLog5 RHBall0504 RHBallDot0509 RHBallMisc0512 RHEntryBall0512 RHQForm0512 RHLowBlock0494

def tget (T : List (List Ball)) (i j : Fin 32) : Ball := (T.getD i []).getD j (0, 0)

lemma tget_ofFn (f : Fin 32 → Fin 32 → Ball) (i j : Fin 32) :
    tget (List.ofFn fun i => List.ofFn fun j => f i j) i j = f i j := by
  simp only [tget, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt, dite_true,
    Option.getD_some, Fin.eta]

def aTab : List (List Ball) := {mat(st['A'])}
def tTab : List (List Ball) := {mat(st['At'])}

theorem aTab_eq : (List.ofFn fun i : Fin 32 => List.ofFn fun j : Fin 32 => entryB (degree {ob} j) (degree {ob} i)) = aTab := by
  decide +kernel
theorem tTab_eq : (List.ofFn fun i : Fin 32 => List.ofFn fun j : Fin 32 => entryB (degree {ob} j) (degree {ob} (32 + i))) = tTab := by
  decide +kernel

def BQ (i j : Fin 32) : ℚ := RHBQ0512.{dq}Q i j
def bB (i j : Fin 32) : Ball := qBall S128 (BQ i j)
def wq (i : Fin 32) : ℚ := harmonic (degree {ob} (32 + i)) + ({'(-16811071618091732846084088270431737827926921338759786126097413044023574083070857 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000' if o else '(-402335143495720182899444246584910110815483700126924367402028335615165576796512809 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000'})
def wB (i : Fin 32) : Ball := qBall S128 (1 / wq i)

def baTab : List (List Ball) := {mat(st['BA'])}
theorem baTab_eq : (List.ofFn fun p : Fin 32 => List.ofFn fun j : Fin 32 =>
    bsum (List.ofFn fun i : Fin 32 => mulB S128 (bB i p) (tget aTab i j))) = baTab := by decide +kernel
def t1Tab : List (List Ball) := {mat(st['T1'])}
theorem t1Tab_eq : (List.ofFn fun p : Fin 32 => List.ofFn fun q : Fin 32 =>
    bsum (List.ofFn fun j : Fin 32 => mulB S128 (tget baTab p j) (bB j q))) = t1Tab := by decide +kernel
def gTab : List (List Ball) := {mat(st['G'])}
theorem gTab_eq : (List.ofFn fun i : Fin 32 => List.ofFn fun p : Fin 32 =>
    bsum (List.ofFn fun j : Fin 32 => mulB S128 (bB j p) (tget tTab i j))) = gTab := by decide +kernel
def t2Tab : List (List Ball) := {mat(st['T2'])}
theorem t2Tab_eq : (List.ofFn fun p : Fin 32 => List.ofFn fun q : Fin 32 =>
    bsum (List.ofFn fun i : Fin 32 => mulB S128 (mulB S128 (tget gTab i p) (tget gTab i q)) (wB i))) = t2Tab := by decide +kernel

def mB (p q : Fin 32) : Ball := sub (tget t1Tab p q) (tget t2Tab p q)

def rowOK (p : Fin 32) : Bool :=
  decide ((1 - ({eta} : ℚ)) ≤ (((mB p p).1 - (mB p p).2 : ℤ) : ℚ) / S128 - (1/2) * ∑ q ∈ univ.erase p,
    ((((mB p q).1.natAbs + (mB p q).2 : ℕ) : ℚ) + (((mB q p).1.natAbs + (mB q p).2 : ℕ) : ℚ)) / S128)

theorem rows_ok : ∀ p : Fin 32, rowOK p = true := by decide +kernel

end RHT5{suf}0512
'''
  open(f'T5Tab0512_{suf}.lean','w').write(L)
print('ok')
