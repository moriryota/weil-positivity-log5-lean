import Ball0504
import Sparse0504

/-! # 0504: ball vectors (lists) and enclosure of the sparse Legendre operations

`VecMem S c bs`: every coefficient `c l` lies in the ball `bs[l]` (zero ball beyond the length;
hence `c l = 0` there). List operations are O(length) by structural recursion.
Enclosure lemmas for `add`, `sub`, scaling, reflection `(−1)^l`, `ImS` and `XS`. -/

namespace RHBallVec0504
open RHBall0504 RHSparse0504

def gz (bs : List Ball) (l : ℕ) : Ball := bs.getD l (0, 0)

@[simp] lemma gz_nil (l : ℕ) : gz [] l = (0, 0) := by simp [gz]
@[simp] lemma gz_cons_zero (b : Ball) (bs : List Ball) : gz (b :: bs) 0 = b := by simp [gz]
@[simp] lemma gz_cons_succ (b : Ball) (bs : List Ball) (l : ℕ) : gz (b :: bs) (l + 1) = gz bs l := by
  simp [gz]

lemma gz_drop_one (bs : List Ball) (l : ℕ) : gz (bs.drop 1) l = gz bs (l + 1) := by
  cases bs with
  | nil => simp
  | cons b bs => simp

lemma gz_of_len : ∀ (bs : List Ball) (l : ℕ), bs.length ≤ l → gz bs l = (0, 0)
  | [], l, _ => by simp
  | b :: bs, 0, h => by simp at h
  | b :: bs, l + 1, h => by simp only [gz_cons_succ]; exact gz_of_len bs l (by simp at h; omega)

def VecMem (S : ℕ) (c : ℕ → ℝ) (bs : List Ball) : Prop := ∀ l, mem S (c l) (gz bs l)

lemma zero_of_len {S : ℕ} (hS : 0 < S) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs)
    {l : ℕ} (hl : bs.length ≤ l) : c l = 0 := by
  have := h l
  rw [gz_of_len bs l hl] at this
  exact (mem_zero S hS).mp this

/-- Index-carrying map. -/
def mapI (f : ℕ → Ball → Ball) : ℕ → List Ball → List Ball
  | _, [] => []
  | i, b :: bs => f i b :: mapI f (i + 1) bs

lemma gz_mapI (f : ℕ → Ball → Ball) : ∀ (i : ℕ) (bs : List Ball) (l : ℕ),
    gz (mapI f i bs) l = if l < bs.length then f (i + l) (gz bs l) else (0, 0)
  | i, [], l => by simp [mapI]
  | i, b :: bs, 0 => by simp [mapI]
  | i, b :: bs, l + 1 => by
      simp only [mapI, gz_cons_succ, gz_mapI f (i + 1) bs l, List.length_cons]
      rw [show i + 1 + l = i + (l + 1) by ring]
      by_cases h : l < bs.length
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

/-- Pointwise map with index, enclosure form. -/
lemma vecMem_mapI {S : ℕ} (hS : 0 < S) {c d : ℕ → ℝ} {bs : List Ball} (f : ℕ → Ball → Ball)
    (h : VecMem S c bs) (hf : ∀ l, mem S (c l) (gz bs l) → mem S (d l) (f l (gz bs l)))
    (hz : ∀ l, c l = 0 → d l = 0) : VecMem S d (mapI f 0 bs) := by
  intro l
  rw [gz_mapI, zero_add]
  split_ifs with hl
  · exact hf l (h l)
  · rw [hz l (zero_of_len hS h (by omega))]
    exact (mem_zero S hS).mpr rfl

/-- Padded pointwise combination (structural in the first list). -/
def zipP (f : Ball → Ball → Ball) : List Ball → List Ball → List Ball
  | [], bs => bs.map (f (0, 0))
  | a :: as, [] => (a :: as).map (fun a => f a (0, 0))
  | a :: as, b :: bs => f a b :: zipP f as bs

lemma gz_map_left (f : Ball → Ball → Ball) (hf : f (0, 0) (0, 0) = (0, 0)) :
    ∀ (as : List Ball) (l : ℕ), gz (as.map (fun a => f a (0, 0))) l = f (gz as l) (0, 0)
  | [], l => by simp [hf]
  | a :: as, 0 => by simp
  | a :: as, l + 1 => by simp only [List.map_cons, gz_cons_succ]; exact gz_map_left f hf as l

lemma gz_map_right (f : Ball → Ball → Ball) (hf : f (0, 0) (0, 0) = (0, 0)) :
    ∀ (bs : List Ball) (l : ℕ), gz (bs.map (f (0, 0))) l = f (0, 0) (gz bs l)
  | [], l => by simp [hf]
  | b :: bs, 0 => by simp
  | b :: bs, l + 1 => by simp only [List.map_cons, gz_cons_succ]; exact gz_map_right f hf bs l

lemma gz_zipP (f : Ball → Ball → Ball) (hf : f (0, 0) (0, 0) = (0, 0)) :
    ∀ (as bs : List Ball) (l : ℕ), gz (zipP f as bs) l = f (gz as l) (gz bs l)
  | [], bs, l => by simp only [zipP, gz_map_right f hf, gz_nil]
  | a :: as, [], l => by simp only [zipP]; rw [gz_map_left f hf]; simp
  | a :: as, b :: bs, 0 => by simp [zipP]
  | a :: as, b :: bs, l + 1 => by simp only [zipP, gz_cons_succ]; exact gz_zipP f hf as bs l

def vadd : List Ball → List Ball → List Ball := zipP add
def vsub : List Ball → List Ball → List Ball := zipP sub

lemma vecMem_vadd {S : ℕ} {c d : ℕ → ℝ} {as bs : List Ball} (hc : VecMem S c as) (hd : VecMem S d bs) :
    VecMem S (fun l => c l + d l) (vadd as bs) := by
  intro l; rw [vadd, gz_zipP add (by rfl)]; exact mem_add (hc l) (hd l)

lemma vecMem_vsub {S : ℕ} {c d : ℕ → ℝ} {as bs : List Ball} (hc : VecMem S c as) (hd : VecMem S d bs) :
    VecMem S (fun l => c l - d l) (vsub as bs) := by
  intro l; rw [vsub, gz_zipP sub (by rfl)]; exact mem_sub (hc l) (hd l)

/-- Scale by the rational `a/d`. -/
def vsmul (a : ℤ) (d : ℕ) (bs : List Ball) : List Ball := mapI (fun _ b => smul a d b) 0 bs

lemma vecMem_vsmul {S : ℕ} (hS : 0 < S) (a : ℤ) {d : ℕ} (hd : 0 < d) {c : ℕ → ℝ} {bs : List Ball}
    (h : VecMem S c bs) : VecMem S (fun l => c l * a / d) (vsmul a d bs) :=
  vecMem_mapI hS _ h (fun l hm => mem_smul hS a hd hm) (fun l hl => by simp [hl])

/-- Reflection: coefficient `l` multiplied by `(−1)^l`. -/
def vrefl (bs : List Ball) : List Ball := mapI (fun l b => if l % 2 = 0 then b else neg b) 0 bs

lemma vecMem_vrefl {S : ℕ} (hS : 0 < S) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs) :
    VecMem S (fun l => (-1) ^ l * c l) (vrefl bs) := by
  refine vecMem_mapI hS _ h (fun l hm => ?_) (fun l hl => by simp [hl])
  rcases Nat.even_or_odd l with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow, one_mul]; exact hm
  · rw [if_neg (by rw [Nat.odd_iff.mp ho]; omega), ho.neg_one_pow, neg_one_mul]; exact mem_neg hm

/-- `ImS` on balls: `A_l = b_l/(2l+1)`, `out_0 = A_0 − A_1`, `out_{m+1} = A_m − A_{m+2}`. -/
def vIm (bs : List Ball) : List Ball :=
  let A := mapI (fun l b => smul 1 (2 * l + 1) b) 0 bs
  vsub (gz A 0 :: A) (A.drop 1)

lemma vecMem_vIm {S : ℕ} (hS : 0 < S) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs) :
    VecMem S (ImS c) (vIm bs) := by
  have hA : VecMem S (Ar c) (mapI (fun l b => smul 1 (2 * l + 1) b) 0 bs) := by
    refine vecMem_mapI hS _ h (fun l hm => ?_) (fun l hl => by simp [Ar, hl])
    have := mem_smul hS 1 (d := 2 * l + 1) (by omega) hm
    have e : c l * ((1 : ℤ) : ℝ) / ((2 * l + 1 : ℕ) : ℝ) = Ar c l := by unfold Ar; push_cast; ring
    rwa [e] at this
  intro m
  unfold vIm
  simp only
  rw [vsub, gz_zipP sub (by rfl), gz_drop_one]
  cases m with
  | zero => simp only [gz_cons_zero, ImS]; exact mem_sub (hA 0) (hA 1)
  | succ m => simp only [gz_cons_succ, ImS]; exact mem_sub (hA m) (hA (m + 2))

/-- `XS` on balls: `B_l = (l+1)/(2l+1) b_l`, `C_l = l/(2l+1) b_l`, `out_0 = C_1`, `out_{m+1} = B_m + C_{m+2}`. -/
def vX (bs : List Ball) : List Ball :=
  let B := mapI (fun l b => smul ((l : ℤ) + 1) (2 * l + 1) b) 0 bs
  let C := mapI (fun l b => smul (l : ℤ) (2 * l + 1) b) 0 bs
  vadd ((0, 0) :: B) (C.drop 1)

lemma vecMem_vX {S : ℕ} (hS : 0 < S) {c : ℕ → ℝ} {bs : List Ball} (h : VecMem S c bs) :
    VecMem S (XS c) (vX bs) := by
  have hB : VecMem S (Bx c) (mapI (fun l b => smul ((l : ℤ) + 1) (2 * l + 1) b) 0 bs) := by
    refine vecMem_mapI hS _ h (fun l hm => ?_) (fun l hl => by simp [Bx, hl])
    have := mem_smul hS ((l : ℤ) + 1) (d := 2 * l + 1) (by omega) hm
    have e : c l * (((l : ℤ) + 1 : ℤ) : ℝ) / ((2 * l + 1 : ℕ) : ℝ) = Bx c l := by unfold Bx; push_cast; ring
    rwa [e] at this
  have hC : VecMem S (Cx c) (mapI (fun l b => smul (l : ℤ) (2 * l + 1) b) 0 bs) := by
    refine vecMem_mapI hS _ h (fun l hm => ?_) (fun l hl => by simp [Cx, hl])
    have := mem_smul hS (l : ℤ) (d := 2 * l + 1) (by omega) hm
    have e : c l * ((l : ℤ) : ℝ) / ((2 * l + 1 : ℕ) : ℝ) = Cx c l := by unfold Cx; push_cast; ring
    rwa [e] at this
  intro m
  unfold vX
  simp only
  rw [vadd, gz_zipP add (by rfl), gz_drop_one]
  cases m with
  | zero =>
      simp only [gz_cons_zero, XS]
      have := mem_add ((mem_zero S hS).mpr rfl) (hC 1)
      rwa [zero_add] at this
  | succ m => simp only [gz_cons_succ, XS]; exact mem_add (hB m) (hC (m + 2))

/-- Unit vector `e_n` (value 1 = `S/S` at index `n`). -/
def vunit (S n : ℕ) : List Ball := List.replicate n (0, 0) ++ [((S : ℤ), 0)]

lemma gz_vunit (S : ℕ) : ∀ (n l : ℕ), gz (vunit S n) l = if l = n then ((S : ℤ), 0) else (0, 0)
  | 0, 0 => by simp [vunit]
  | 0, l + 1 => by simp [vunit]
  | n + 1, 0 => by simp [vunit, List.replicate_succ]
  | n + 1, l + 1 => by
      have h := gz_vunit S n l
      simp only [vunit, List.replicate_succ, List.cons_append, gz_cons_succ] at h ⊢
      rw [h]; simp

lemma vecMem_vunit {S : ℕ} (hS : 0 < S) (n : ℕ) :
    VecMem S (fun l => if l = n then 1 else 0) (vunit S n) := by
  intro l
  rw [gz_vunit]
  by_cases h : l = n
  · rw [if_pos h]; simp only [if_pos h]
    have : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
    simp [mem, this]
  · rw [if_neg h]; simp only [if_neg h]; exact (mem_zero S hS).mpr rfl

end RHBallVec0504

