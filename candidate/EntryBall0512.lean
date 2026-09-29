import EntryRepr0512
import RpAll0512
import TpAll0512
import PrAll0512
import CcEncl0510
import BallMisc0512
import PrEncl0511
import Const0510

/-! # 0512: ball enclosure of every Weil column entry `colEntry n k` (n < 64, k < 128)

`entryB n k` is computed from the proved coarse tables (Rp, Tp, Pr, Cc/Ss) and constant balls
(L, c_n, h0, Cd, H_n) at scale `2^128`; `entry_mem` proves `mem (2^128) (colEntry n k) (entryB n k)`.
 -/

open Finset
open scoped BigOperators

namespace RHEntryBall0512
open RHConditionalLog5 RHLog5Bridge RHBall0504 RHBallVec0504 RHBallDot0509 RHBallMisc0512 RHRpExact0506 RHEntryRepr0512
  RHTpEncl0509 RHTpErr0508 RHCcSs0510 RHCcEncl0510

def S128 : ℕ := 2 ^ 128
lemma hS : 0 < S128 := by unfold S128; positivity

def LB : Ball := (273831671127684886333697169969646442746, 2)
def h0B : Ball := (-1828059289427529715792100834798405240356, 1701414)
def CdB : Ball := (1184592912812379483222007122388350781200, 3494541564)
def cT : List Ball := [(268226900568881400449905774858749418562, 4), (464582619742027981983430168942564510938, 4), (599773583066095823461042542978122390932, 4), (709661673842909544940016417829275208124, 4), (804680701706644201349717324576248255688, 4), (889607987866944955292821161610569820748, 4), (967105843459882968706458270022933304124, 4), (1038838318908110378028927883875793528700, 4), (1105927842677543777035151948922528906064, 4), (1169173953518886426249546876950713154532, 4), (1229170075280292680877269945839159978554, 4), (1286371025148707846516046688111694949740, 4), (1341134502844407002249528874293747092812, 4), (1393747859226083945950290506827693532812, 4), (1444446065270305996476104584842803662562, 4), (1493424178139769595203967389123883942744, 4), (1540846233804666002877654783196071612496, 4), (1586851743739030154471186881627644961286, 4), (1631560540398418009539613029730683060772, 4), (1675076457169270522855613209021445404432, 4), (1717490168164095244791340451705660775762, 4), (1758881411044505109845323972196048555508, 4), (1799320749198287470383127628934367172794, 4), (1838870984836365212471746635999212203204, 4), (1877588303982169803149340424011245929936, 4), (1915523213022545977770611570857394222284, 4), (1952721311402575755492898753245581260446, 4), (1989223934197297057531170329248036143936, 4), (2025068690380884238667482110513592303526, 4), (2060289916768639328408690928390358758176, 4), (2094919063237552371001993980599931235432, 4), (2128985021528728634820049253487825624370, 4), (2162514407413568726390557193830414154604, 4), (2195531804062249398885092535262543100268, 4), (2228059972942023987824074337801291154610, 4), (2260120037388277712148463168681068341566, 4), (2291731643055435716897069029193064418338, 4), (2322913098710139909917150844712822554686, 4), (2353681500232502014282098174656978554890, 4), (2384052840210195206528118540407679555448, 4), (2414042105119932604049151973728744767062, 4), (2443663361772536154987197487323465289408, 4), (2472929834436680917586193259406333192514, 4), (2501853973841120742590716883579747391042, 4), (2530447519076849863061073885692731775302, 4), (2558721553272212077868320950875731279760, 4), (2586686553789874790715698067973280640606, 4), (2614352437590409497715301555490009939542, 4), (2641728602319415620707097444012279360322, 4), (2668823963600834865878463484831709462242, 4), (2695646988956018240111694452551435027334, 4), (2722205728714349888759137605072068229882, 4), (2748507844235268301656722216039282129880, 4), (2774560633722099622307774800418102775304, 4), (2800371055874195439926165563115681818532, 4), (2825945751594593759394450263340577478394, 4), (2851291063945087770229628846435138381064, 4), (2876413056518602262651793217036246905348, 4), (2901317530379648906119374810068799912372, 4), (2926010039706945730761365522530852367198, 4), (2950495906257695404948963523446243604186, 4), (2974780232760228035690892964410061920146, 4), (2998867915330479117305212714890611954656, 4), (3022763654997881379469950442582387959814, 4), (3046471968417521485173950966030197723710, 4), (3069997197837695943082245029464432170980, 4), (3093343520385164461566736987092524584686, 4), (3116514956724331134086783651627380586098, 4), (3139515379141187889232685025954295409588, 4), (3162348519098047472333021247050864483600, 4), (3185017974300803078208276489065509145854, 4), (3207527215316616495354445897333578526456, 4), (3229879591776502348152163995486749827442, 4), (3252078338194195873884011182597951576562, 4), (3274126579429924821656661657245554754270, 4), (3296027335825216876623426633124940298198, 4), (3317783528032631331105455846767586718192, 4), (3339397981562280238596439403610689442488, 4), (3360873431065176028649263139880478499530, 4), (3382212524371788453824173009020370926798, 4), (3403417826302695218994341156392503040322, 4), (3424491822266851327736890001362079725088, 4), (3445436921661767593621766360961996671350, 4), (3466255461088766091595660988159473127524, 4), (3486949707395458205848775073163742441312, 4), (3507521860556659278748640630852139463598, 4), (3527974056404103711526918053904872403982, 4), (3548308369214547724700082089146376040618, 4), (3568526814165136732795442375811631285238, 4), (3588631349664264064420678029928583566664, 4), (3608623879565551878896492587932216777986, 4), (3628506255272038503752399077124155550714, 4), (3648280277737154479750521876693461950852, 4), (3667947699368608255644619782781694579206, 4), (3687510225840878042631809837517479935662, 4), (3706969517821615506568271658495403699606, 4), (3726327192616906761292966748157871462190, 4), (3745584825740003838598267205936168475128, 4), (3764743952407833020759537057183534552594, 4), (3783806068969302935027706892820231481042, 4), (3802772634269173140122553485212213645296, 4), (3821645070951001283851359560935716932736, 4), (3840424766702462147788366224590652139892, 4), (3859113075446123539548140064335084849218, 4), (3877711318478570701163475515021065299352, 4), (3896220785560591450970992151747632470592, 4), (3914642735960967553583453595027635036592, 4), (3932978399456262804383668568558387659888, 4), (3951228977288854097284273947414722147558, 4), (3969395643085317473780775938355304113254, 4), (3987479543737156057122226712474376770784, 4), (4005481800245740153371617764367055070240, 4), (4023403508533221006748586622881241278436, 4), (4041245740221078139770233163787233741792, 4), (4059009543377865348455753981326618047560, 4), (4076695943237631763144318981937380270396, 4), (4094305942890411470920435667129969205496, 4), (4111840523946097607931878836490534049636, 4), (4129300647172944184459756734721627072436, 4), (4146687253111870848664061968159768795562, 4), (4164001262667682000756611554849284910336, 4), (4181243577678251837850871520483080598436, 4), (4198415081462670764227297800846856736518, 4), (4215516639349295886970880586056748177252, 4), (4232549099184598797219593832219590918870, 4), (4249513291823657294891469955471483373970, 4), (4266410031603093948466307692079781645076, 4), (4283240116797223205004281541288239477388, 4)]
def cB (n : ℕ) : Ball := cT.getD n (0, 0)

/-- Ball of a rational: `(⌊q S⌋, 1)`. -/
def qBall (S : ℕ) (q : ℚ) : Ball := (⌊q * S⌋, 1)
lemma mem_qBall {S : ℕ} (hS : 0 < S) (q : ℚ) : mem S (q : ℝ) (qBall S q) := by
  unfold mem qBall; simp only
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have h1 := Int.floor_le (q * S)
  have h2 := Int.lt_floor_add_one (q * S)
  have h1' : ((⌊q * S⌋ : ℤ) : ℝ) ≤ (q : ℝ) * S := by exact_mod_cast h1
  have h2' : (q : ℝ) * S < ((⌊q * S⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast h2
  have a1 : ((⌊q * S⌋ : ℤ) : ℝ) / S ≤ q := by rw [div_le_iff₀ hS']; linarith
  have a2 : (q : ℝ) ≤ (((⌊q * S⌋ : ℤ) : ℝ) + 1) / S := by rw [le_div_iff₀ hS']; linarith
  rw [add_div] at a2
  have a3 : (0:ℝ) ≤ 1 / S := by positivity
  push_cast
  rw [abs_le]; constructor <;> linarith

lemma L_mem : mem S128 halfWidth LB := by
  have h := Trial0456.log5_bounds
  apply RHPrEncl0511.mem_of_bounds hS (lo := Trial0456.lo / 2) (hi := Trial0456.hi / 2)
  · unfold halfWidth; push_cast; linarith [h.1]
  · unfold halfWidth; push_cast; linarith [h.2]
  · unfold S128; decide +kernel
  · unfold S128; decide +kernel

lemma h0_mem : mem S128 RHLowBlock0494.h0c h0B :=
  RHPrEncl0511.mem_of_bounds hS RHEntry00Bounds0495.b_h.1 RHEntry00Bounds0495.b_h.2
    (by unfold S128; decide +kernel) (by unfold S128; decide +kernel)

noncomputable def Cd : ℝ := g0 - Real.log halfWidth - (Real.log 2 - 1)
lemma Cd_mem : mem S128 Cd CdB := by
  have h2 := Trial0455.log2_bounds
  have hp := RHPi0466.pi_bounds
  have hl := RHConst0510.logL_bounds
  apply RHPrEncl0511.mem_of_bounds hS
    (lo := Trial0455.lo + RHPi0466.piLo / 2 + 1 - RHConst0510.LLhi)
    (hi := Trial0455.hi + RHPi0466.piHi / 2 + 1 - RHConst0510.LLlo)
  · unfold Cd g0; push_cast; linarith [h2.1, hp.1, hl.2]
  · unfold Cd g0; push_cast; linarith [h2.2, hp.2, hl.1]
  · unfold S128; decide +kernel
  · unfold S128; decide +kernel

def Llo : ℚ := Trial0456.lo / 2
def Lhi : ℚ := Trial0456.hi / 2
def cOK (n : ℕ) : Bool :=
  let b := cB n
  decide (0 ≤ b.1 - b.2) &&
  decide ((((b.1 - b.2 : ℤ) : ℚ) / S128) ^ 2 * 2 * Lhi ≤ 2 * n + 1) &&
  decide ((2 * n + 1 : ℚ) ≤ (((b.1 + b.2 : ℤ) : ℚ) / S128) ^ 2 * 2 * Llo)

lemma cAll : (List.range 128).all cOK = true := by decide +kernel

lemma c_mem (n : ℕ) (hn : n < 128) : mem S128 (cc n) (cB n) := by
  have hc : cOK n = true := List.all_eq_true.mp cAll n (List.mem_range.mpr hn)
  unfold cOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h0, h1⟩, h2⟩ := hc
  have hL := Trial0456.log5_bounds
  have hLlo : ((Llo : ℚ) : ℝ) ≤ halfWidth := by unfold Llo halfWidth; push_cast; linarith [hL.1]
  have hLhi : halfWidth ≤ ((Lhi : ℚ) : ℝ) := by unfold Lhi halfWidth; push_cast; linarith [hL.2]
  have hLpos := halfWidth_pos
  have hS' : (0:ℝ) < S128 := by exact_mod_cast hS
  generalize cB n = bb at h0 h1 h2 ⊢
  obtain ⟨m, e⟩ := bb
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h1' h2'
  have h0' : (0:ℝ) ≤ (m : ℝ) - e := by
    have : (0:ℤ) ≤ m - e := h0
    have h := (Int.cast_le (R := ℝ)).mpr this; push_cast at h; exact h
  have hlo0 : 0 ≤ ((m : ℝ) - e) / S128 := div_nonneg h0' hS'.le
  have hn1 : (0:ℝ) < 2 * n + 1 := by positivity
  have hb := sqrt_bounds (a := (2 * n + 1) / (2 * halfWidth)) (lo := ((m : ℝ) - e) / S128) (hi := ((m : ℝ) + e) / S128) hlo0
    (by rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (((m : ℝ) - e) / S128)])
    (by rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (((m : ℝ) + e) / S128)])
    (le_trans hlo0 (by apply div_le_div_of_nonneg_right _ hS'.le; linarith [(Nat.cast_nonneg e : (0:ℝ) ≤ e)]))
  exact mem_of_bounds' hS hb.1 hb.2

def ceB (n : ℕ) (odd : Bool) : Ball :=
  if n < 40 then (if odd then (ccSpec.getD n ((0,0),(0,0))).2 else (ccSpec.getD n ((0,0),(0,0))).1) else (0, 0)

lemma ce_mem' (n : ℕ) (odd : Bool) : mem S128 (ce 40 odd n) (ceB n odd) := by
  unfold ceB
  by_cases h : n < 40
  · rw [if_pos h]
    have := ce_mem n h odd
    cases odd
    · simpa [S128] using this
    · simpa [S128] using this
  · rw [if_neg h, ce_zero odd (by omega)]; exact (mem_zero _ hS).mpr rfl

/-- Cc/Ss ball: `L c_n (ce + R)`, `|R| ≤ 10⁻⁶⁰ ≤ 1/S`. -/
def hypB (n : ℕ) (odd : Bool) : Ball := mulB S128 (mulB S128 LB (cB n)) (add (ceB n odd) (0, 1))

lemma hyp_mem (n : ℕ) (hn : n < 128) (odd : Bool) :
    mem S128 (∫ y in Set.Icc (-halfWidth) halfWidth, (basisPoly n).eval y *
      (if odd then Real.sinh (y / 2) else Real.cosh (y / 2))) (hypB n odd) := by
  obtain ⟨R, hR, he⟩ := hyp_eq n 40 (by norm_num) odd
  rw [he]
  have hR' : mem S128 R (0, 1) := by
    unfold mem; simp only; push_cast
    have := bnd_le
    have hs : (1:ℝ) / 10 ^ 60 ≤ 1 / (S128 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hS)]; unfold S128; norm_num
    rw [zero_div, sub_zero]; linarith
  exact mem_mulB hS (mem_mulB hS L_mem (c_mem n hn)) (mem_add (ce_mem' n odd) hR')

def rpB (n k : ℕ) : Ball := ((RHRpAll0512.rpSpecT n).getD k ((0,0),(0,0))).1
def tpB (n k : ℕ) : Ball := ((RHTpAll0512.tpSpecT n).getD k ((0,0),(0,0))).2
def prB (n k : ℕ) : Ball := ((RHPrAll0512.prSpecT n).getD k ((0,0),(0,0))).1

/-- `4·10⁻²⁴ ≤ eR/S`, `2·10⁻²⁴ ≤ eT/S`. -/
def eR : ℕ := 1400000000000000
def eT : ℕ := 700000000000000

lemma err_mem {E : ℝ} {b : ℚ} {e : ℕ} (hE : |E| ≤ b) (hb : b ≤ (e : ℚ) / S128) : mem S128 E (0, e) := by
  unfold mem; simp only; push_cast
  rw [zero_div, sub_zero]
  have := (Rat.cast_le (K := ℝ)).mpr hb; push_cast at this; linarith

def sgn (n k : ℕ) : ℤ := if (n + k) % 2 = 0 then 1 else 0

lemma sgn_eq (n k : ℕ) : (1 + (-1 : ℝ) ^ (n + k)) / 2 = (sgn n k : ℝ) := by
  unfold sgn
  rcases Nat.even_or_odd (n + k) with h | h
  · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]; norm_num
  · rw [if_neg (by rw [Nat.odd_iff.mp h]; omega), h.neg_one_pow]; norm_num

lemma sgn_eq2 (n k : ℕ) : (1 + (-1 : ℝ) ^ (n + k)) = 2 * (sgn n k : ℝ) := by
  rw [← sgn_eq]; ring

def entryB (n k : ℕ) : Ball :=
  let cc2 := mulB S128 (cB n) (cB k)
  let FR := smul 1 (2 * k + 1) (mulB S128 (mulB S128 LB LB) cc2)
  let FT := mulB S128 LB cc2
  let diag := if n = k then add (add h0B (qBall S128 (harmonic n))) CdB else (0, 0)
  let rpart := add (mulB S128 FR (rpB n k)) (0, eR)
  let tpart := add (neg (smul (sgn n k) 1 (mulB S128 FT (tpB n k)))) (0, eT)
  let ccpart := smul 2 1 (mulB S128 (hypB n false) (hypB k false))
  let sspart := smul 2 1 (mulB S128 (hypB n true) (hypB k true))
  let prpart := smul (2 * sgn n k) 1 (mulB S128 FT (prB n k))
  sub (add (add (add diag rpart) tpart) ccpart) (add sspart prpart)

theorem entry_mem (n k : ℕ) (hn : n < 64) (hk : k < 128) :
    mem S128 (RHColDecomp0499.colEntry n k) (entryB n k) := by
  have hS1 := hS
  rw [RHColDecomp0499.colEntry_decomp]
  obtain ⟨ER, hER, hRp⟩ := Rp_repr (n := n) (k := k) (by omega) (by omega)
  obtain ⟨ET, hET, hTp⟩ := Tp_repr (n := n) (k := k) (by omega) (by omega)
  rw [hRp, hTp, RHPrEncl0511.Pr_T, sgn_eq]
  have hcn := c_mem n (by omega)
  have hck := c_mem k hk
  have hcc := mem_mulB hS hcn hck
  have hL := L_mem
  have hFR : mem S128 (halfWidth ^ 2 * cc n * cc k / (2 * k + 1)) (smul 1 (2 * k + 1) (mulB S128 (mulB S128 LB LB) (mulB S128 (cB n) (cB k)))) := by
    have := mem_smul hS 1 (d := 2 * k + 1) (by omega) (mem_mulB hS (mem_mulB hS hL hL) hcc)
    convert this using 1; push_cast; ring
  have hFT : mem S128 (halfWidth * cc n * cc k) (mulB S128 LB (mulB S128 (cB n) (cB k))) := by
    have := mem_mulB hS hL hcc; convert this using 1; ring
  have hdiag : mem S128 ((RHLowBlock0494.h0c + (harmonic n : ℝ)) * (if n = k then 1 else 0) +
      (if n = k then g0 - Real.log halfWidth - (Real.log 2 - 1) else 0))
      (if n = k then add (add h0B (qBall S128 (harmonic n))) CdB else (0, 0)) := by
    split_ifs with h
    · have := mem_add (mem_add h0_mem (mem_qBall hS (harmonic n))) Cd_mem
      convert this using 1; unfold Cd; ring
    · simp only [mul_zero, add_zero]; exact (mem_zero _ hS).mpr rfl
  have hrp := mem_add (mem_mulB hS hFR (RHRpAll0512.rp_all n k hn hk))
    (err_mem (b := 4 / 10 ^ 24) (e := eR) (by push_cast; exact hER) (by decide +kernel))
  have htp := mem_add (mem_neg (mem_smul hS (sgn n k) (d := 1) (by norm_num) (mem_mulB hS hFT (RHTpAll0512.tp_all n k hn hk))))
    (err_mem (b := 2 / 10 ^ 24) (e := eT) (by push_cast; exact hET) (by decide +kernel))
  have hcc2 := mem_smul hS 2 (d := 1) (by norm_num) (mem_mulB hS (hyp_mem n (by omega) false) (hyp_mem k hk false))
  have hss2 := mem_smul hS 2 (d := 1) (by norm_num) (mem_mulB hS (hyp_mem n (by omega) true) (hyp_mem k hk true))
  have hpr := mem_smul hS (2 * sgn n k) (d := 1) (by norm_num) (mem_mulB hS hFT (RHPrAll0512.pr_all n k hn hk))
  have hfin := mem_sub (mem_add (mem_add (mem_add hdiag hrp) htp) hcc2) (mem_add hss2 hpr)
  rw [sgn_eq2]
  convert hfin using 1
  · unfold RHColDecomp0499.Cc RHColDecomp0499.Ss
    simp only [Bool.false_eq_true, if_false, if_true]
    push_cast
    ring
  · rfl

end RHEntryBall0512

