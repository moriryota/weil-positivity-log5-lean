import FullParallelogram
namespace RHTargetFormBinding
set_option maxHeartbeats 1000000

theorem targetQ_real_parity_split_of_test {L : ℝ} (hL : 0 < L)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hs : ∀ x, u x ≠ 0 → |x| ≤ L) :
    targetQ_real u = targetQ_real (fun x => (u x+u (-x))/2) +
      targetQ_real (fun x => (u x-u (-x))/2) := by
  let e : ℝ → ℝ := fun x => (u x+u (-x))/2
  let o : ℝ → ℝ := fun x => (u x-u (-x))/2
  have hr : ContDiff ℝ 1 (fun x => u (-x)) := hu.comp contDiff_id.neg
  have he : ContDiff ℝ 1 e := (hu.add hr).div_const 2
  have ho : ContDiff ℝ 1 o := (hu.sub hr).div_const 2
  have hz (x : ℝ) (h : ¬ |x| ≤ L) : u x = 0 ∧ u (-x) = 0 := by
    constructor
    · by_contra hn
      exact h (hs x hn)
    · by_contra hn
      have hh := hs (-x) hn
      rw [abs_neg] at hh
      exact h hh
  have hse : ∀ x, e x ≠ 0 → |x| ≤ L := by
    intro x hn
    by_contra h
    rcases hz x h with ⟨hx, hm⟩
    exact hn (by simp [e, hx, hm])
  have hso : ∀ x, o x ≠ 0 → |x| ≤ L := by
    intro x hn
    by_contra h
    rcases hz x h with ⟨hx, hm⟩
    exact hn (by simp [o, hx, hm])
  have hep : (fun x => e x+o x) = u := by funext x; dsimp [e,o]; ring
  have hem : (fun x => e x-o x) = (fun x => u (-x)) := by
    funext x; dsimp [e,o]; ring
  have hp := targetQ_real_parallelogram hL e o he ho hse hso
  rw [hep, hem, targetQ_real_reflect] at hp
  change targetQ_real u = targetQ_real e + targetQ_real o
  linarith only [hp]

theorem targetQ_four_parts_of_test (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ RHLog5Bridge.halfWidth) :
    RHTargetLog5.targetQ f =
      targetQ_real (fun x => ((f x).re+(f (-x)).re)/2) +
      targetQ_real (fun x => ((f x).re-(f (-x)).re)/2) +
      targetQ_real (fun x => ((f x).im+(f (-x)).im)/2) +
      targetQ_real (fun x => ((f x).im-(f (-x)).im)/2) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hr := targetQ_real_parity_split_of_test RHLog5Bridge.halfWidth_pos
    (fun x => (f x).re) (Complex.reCLM.contDiff.comp hf1)
    (RHComplexFrequency.re_support hs)
  have hi := targetQ_real_parity_split_of_test RHLog5Bridge.halfWidth_pos
    (fun x => (f x).im) (Complex.imCLM.contDiff.comp hf1)
    (RHComplexFrequency.im_support hs)
  rw [targetQ_split f hf hs, hr, hi]
  ring
end RHTargetFormBinding
