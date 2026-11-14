import MatedCRT.Proofs.LBM.TimeChangeContinuity
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExitTail

/-!
# Exit time of Liouville Brownian motion and the LQG clock at the Brownian exit time

For a time-change clock `f` (continuous, strictly increasing, `f 0 = 0`, `f t → ∞`) and any path `g`, the first exit
time from a set `O` of the time-changed path `t ↦ g (f⁻¹ t)` is the clock evaluated at the first exit time of `g`:
`pathExitTime O (g ∘ f⁻¹) = f (pathExitTime O g)`, with `f ∞ = ∞`. No openness of `O` and no continuity of `g` is
needed, since `f` induces an order isomorphism of `[0, ∞)`.

* `pathExitTime_comp_clockInverse_eq_ofReal`, `pathExitTime_comp_clockInverse_eq_top`: the identity for a general
  path, in the finite and the infinite case.
* `lbmExitTime_eq_ofReal_clock_of_pathExitTime_eq`, `lbmExitTime_eq_ofReal_clock_pathExitTime`,
  `lbmExitTime_eq_top_of_pathExitTime_eq_top`: the same for the Liouville Brownian path `t ↦ b (F⁻¹(t))`.
* `MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_eq_clock`: for almost every environment and Brownian path from `0`,
  the exit time of Liouville Brownian motion from `B_{1/2}` is the LQG clock at the positive and finite Brownian exit
  time.
* `MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_pos_lt_top`: hence `0 < τ^{LBM}_{B_{1/2}} < ∞` almost surely.
-/

namespace MatedCRT

open MeasureTheory Set Filter Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The first exit time from `O` of a path run with a time-change clock `f` is the clock evaluated at the first
exit time of the path, when the latter is finite. -/
theorem pathExitTime_comp_clockInverse_eq_ofReal {α : Type*} {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f)
    (O : Set α) (g : ℝ≥0 → α) {τ : ℝ≥0} (hτ : pathExitTime O g = τ) :
    pathExitTime O (fun t => g (clockInverse f t)) = ENNReal.ofReal (f τ) := by
  have hinv : ∀ s : ℝ≥0, clockInverse f (Real.toNNReal (f s)) = s :=
    clockInverse_clockValue hf.map_zero hf.strictMono
  have hmem : ∀ s : ℝ≥0, g s ∉ O →
      pathExitTime O (fun t => g (clockInverse f t)) ≤ ENNReal.ofReal (f s) := by
    intro s hs
    unfold pathExitTime
    exact sInf_le ⟨Real.toNNReal (f s), rfl, by simpa only [hinv] using hs⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    induction c using ENNReal.recTopCoe with
    | top => exact le_top
    | coe u =>
      obtain ⟨s₀, hs₀⟩ := IsTimeChangeClock.surjective_toNNReal hf u
      have hs₀' : Real.toNNReal (f s₀) = u := hs₀
      have hc' : ((Real.toNNReal (f τ) : ℝ≥0) : ℝ≥0∞) < u := hc
      have hlt : Real.toNNReal (f τ) < Real.toNNReal (f s₀) := by
        rw [hs₀']
        exact ENNReal.coe_lt_coe.mp hc'
      have hτs₀ : τ < s₀ := by
        have h := IsTimeChangeClock.strictMono_clockInverse hf hlt
        rwa [hinv, hinv] at h
      have hlt' : pathExitTime O g < (s₀ : ℝ≥0∞) := by
        rw [hτ]
        exact ENNReal.coe_lt_coe.mpr hτs₀
      unfold pathExitTime at hlt'
      obtain ⟨_, ⟨s, rfl, hs⟩, hss₀⟩ := sInf_lt_iff.mp hlt'
      calc pathExitTime O (fun t => g (clockInverse f t)) ≤ ENNReal.ofReal (f s) := hmem s hs
        _ ≤ ENNReal.ofReal (f s₀) :=
          ENNReal.ofReal_le_ofReal (hf.strictMono.monotone (ENNReal.coe_le_coe.mp hss₀.le))
        _ = (u : ℝ≥0∞) := congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hs₀'
  · unfold pathExitTime
    apply le_sInf
    rintro _ ⟨u, rfl, hu⟩
    obtain ⟨s, hs⟩ := IsTimeChangeClock.surjective_toNNReal hf u
    have hs' : Real.toNNReal (f s) = u := hs
    subst hs'
    simp only [hinv] at hu
    have hτs : (τ : ℝ≥0∞) ≤ s := by
      rw [← hτ]
      unfold pathExitTime
      exact sInf_le ⟨s, rfl, hu⟩
    exact ENNReal.ofReal_le_ofReal (hf.strictMono.monotone (ENNReal.coe_le_coe.mp hτs))

/-- A path which never leaves `O` still never leaves it after any time change. -/
theorem pathExitTime_comp_clockInverse_eq_top {α : Type*} (f : ℝ≥0 → ℝ) (O : Set α) (g : ℝ≥0 → α)
    (hτ : pathExitTime O g = ⊤) : pathExitTime O (fun t => g (clockInverse f t)) = ⊤ := by
  unfold pathExitTime
  rw [sInf_eq_top]
  rintro _ ⟨u, rfl, hu⟩
  have h : pathExitTime O g ≤ (clockInverse f u : ℝ≥0∞) := by
    unfold pathExitTime
    exact sInf_le ⟨clockInverse f u, rfl, hu⟩
  rw [hτ, top_le_iff] at h
  exact absurd h ENNReal.coe_ne_top

/-- **Exit time of Liouville Brownian motion = LQG clock at the Brownian exit time.** If the clock `F b` is a
time-change clock and the path `b` leaves `O` at the finite time `τ`, then the Liouville Brownian path
`t ↦ b (F⁻¹(t))` leaves `O` at the time `F b τ`. -/
theorem lbmExitTime_eq_ofReal_clock_of_pathExitTime_eq {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} (hF : IsTimeChangeClock (F b)) (O : Set ℂ) {τ : ℝ≥0}
    (hτ : pathExitTime O b = τ) : lbmExitTime F O b = ENNReal.ofReal (F b τ) :=
  pathExitTime_comp_clockInverse_eq_ofReal hF O b hτ

/-- The exit time of Liouville Brownian motion from `O` is the LQG clock evaluated at the Brownian exit time
`τ_O b = pathExitTime O b`, when the latter is finite. -/
theorem lbmExitTime_eq_ofReal_clock_pathExitTime {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} (hF : IsTimeChangeClock (F b)) (O : Set ℂ) (hfin : pathExitTime O b ≠ ⊤) :
    lbmExitTime F O b = ENNReal.ofReal (F b (pathExitTime O b).toNNReal) :=
  lbmExitTime_eq_ofReal_clock_of_pathExitTime_eq hF O (ENNReal.coe_toNNReal hfin).symm

/-- If the Brownian path never leaves `O`, neither does the Liouville Brownian path, for any clock. -/
theorem lbmExitTime_eq_top_of_pathExitTime_eq_top (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (O : Set ℂ)
    (b : ContinuousPath ℂ) (h : pathExitTime O b = ⊤) : lbmExitTime F O b = ⊤ :=
  pathExitTime_comp_clockInverse_eq_top (F b) O b h

/-- For almost every environment of a valid mated-CRT setting and almost every planar Brownian path started at `0`,
the exit time of Liouville Brownian motion from `B_{1/2}` is the LQG clock evaluated at the Brownian exit time
`τ ∈ (0, ∞)` of `B_{1/2}`. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_eq_clock {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion 0, ∃ τ : ℝ≥0, 0 < τ ∧
      pathExitTime (ball (0 : ℂ) (1 / 2)) b = τ ∧
      lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b = ENNReal.ofReal (S.clock ω b τ) := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock 0).2, ae_planarBrownianMotion_exit_ball_lt_top,
    ae_planarBrownianMotion_eval_zero 0] with b hb hfin hstart
  have hpos : 0 < ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) b := by
    apply (ContinuousPath.exitTime_pos_iff _ isOpen_ball b).2
    rw [hstart]
    simp
  have hτ : pathExitTime (ball (0 : ℂ) (1 / 2)) b =
      ((ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin.ne).symm
  exact ⟨_, ENNReal.toNNReal_pos hpos.ne' hfin.ne, hτ,
    lbmExitTime_eq_ofReal_clock_of_pathExitTime_eq hb _ hτ⟩

/-- For almost every environment of a valid mated-CRT setting and almost every planar Brownian path started at `0`,
the exit time `T = lbmExitTime (S.clock ω) (ball 0 (1/2)) b` of Liouville Brownian motion from `B_{1/2}` satisfies
`0 < T < ∞`. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_pos_lt_top {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      0 < lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ∧
        lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b < ⊤ := by
  filter_upwards [hS.ae_lbmExitTime_pos (by norm_num : (0 : ℝ) < 1 / 2), hS.ae_lbmExitTime_lt_top]
    with ω hpos hfin
  filter_upwards [hpos, hfin] with b h₁ h₂
  exact ⟨h₁, h₂⟩

end MatedCRT
