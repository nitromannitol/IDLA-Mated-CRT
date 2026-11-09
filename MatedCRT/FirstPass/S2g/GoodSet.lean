import MatedCRT.FirstPass.S2f
import MatedCRT.FirstPass.Frozen.S2g

/-!
# Good set, deterministic part: contact sets of certificates (fp-S2g, q1)

Pure potential theory on `B_R` with pole `0` (Armitage-Gardiner notation; HB `supersolutions`, `leastSupersolution`,
`cluster`). Written argument: `notes/fp-gaps/CHATGPT-cone-good-set.md` Section 4.1; the minimum principle and the
pole behaviour of the disc Green function are the frozen EXTERNAL inputs of `Frozen/S2g.lean`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The contact set of a candidate `w` at time `t` on `B_R` with pole `0`: the points `x ∈ B_R` with `x = 0` or
`-t G_{B_R}(0,x) < w x`. This is the HB `cluster` with the candidate `w` in place of the least supersolution. -/
def certCluster (R t : ℝ) (w : ℂ → ℝ) : Set ℂ :=
  {x ∈ ball (0 : ℂ) R | x = 0 ∨ -t * greenFunction (ball 0 R) 0 x < w x}

/-- The contact set of a candidate is open when `w` is continuous on the closed ball and `t > 0`: away from the pole
this is the continuity of the Green function and of `w`; at the pole `-t G → -∞` while `w` is bounded below. -/
theorem isOpen_certCluster (hpole : FrozenGreenDiscPole) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    {w : ℂ → ℝ} (hw : ContinuousOn w (closedBall (0 : ℂ) R)) : IsOpen (certCluster R t w) := by
  obtain ⟨hGc, hGtop⟩ := hpole R hR
  have hclosed : ∀ y ∈ ball (0 : ℂ) R, closedBall (0 : ℂ) R ∈ 𝓝 y := fun y hy =>
    mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hxb, hxc⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    have hA : Tendsto (fun y => -t * greenFunction (ball 0 R) 0 y) (𝓝[≠] 0) atBot := by
      have h' := tendsto_neg_atTop_atBot.comp (hGtop.const_mul_atTop ht)
      exact Tendsto.congr (fun y => by simp [Function.comp_apply, neg_mul]) h'
    have hwc : ContinuousAt w 0 := hw.continuousAt (hclosed 0 (mem_ball_self hR))
    have hev : ∀ᶠ y in 𝓝 (0 : ℂ), w 0 - 1 < w y :=
      hwc.tendsto.eventually (lt_mem_nhds (sub_one_lt (w 0)))
    have hev2 : ∀ᶠ y in 𝓝[≠] (0 : ℂ), -t * greenFunction (ball 0 R) 0 y < w y := by
      filter_upwards [hA.eventually (eventually_lt_atBot (w 0 - 1)),
        eventually_nhdsWithin_of_eventually_nhds hev] with y h1 h2
      linarith
    have hev3 := eventually_nhdsWithin_iff.mp hev2
    filter_upwards [hev3, isOpen_ball.mem_nhds hxb] with y hy1 hy2
    by_cases hy : y = 0
    · exact ⟨hy2, Or.inl hy⟩
    · exact ⟨hy2, Or.inr (hy1 hy)⟩
  · have hxlt : -t * greenFunction (ball 0 R) 0 x < w x := hxc.resolve_left hx0
    have hGx : ContinuousAt (greenFunction (ball 0 R) 0) x := by
      apply ContinuousOn.continuousAt hGc
      have h1 : closedBall (0 : ℂ) R ∈ 𝓝 x := hclosed x hxb
      have h2 : ({0} : Set ℂ)ᶜ ∈ 𝓝 x := isOpen_compl_singleton.mem_nhds hx0
      exact mem_of_superset (inter_mem h1 h2) (fun y hy => ⟨hy.1, hy.2⟩)
    have hwx : ContinuousAt w x := hw.continuousAt (hclosed x hxb)
    have hlt : ∀ᶠ y in 𝓝 x, -t * greenFunction (ball 0 R) 0 y < w y :=
      (continuousAt_const.mul hGx).eventually_lt hwx hxlt
    filter_upwards [hlt, isOpen_ball.mem_nhds hxb] with y hy1 hy2
    exact ⟨hy2, Or.inr hy1⟩

end MatedCRT
