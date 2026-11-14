import MatedCRT.FirstPass.S6j.WalkDisplacementBlocks
import MatedCRT.FirstPass.S6j.CmpEDistPointwise
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import MatedCRT.FirstPass.S6j.ExitTailAssembly
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import LatticeProb.Prob.ContinuousPathStepTimeLower
import LatticeProb.Prob.ContinuousPathStepTimeStopped
import LatticeProb.Prob.BrownianStepTimeScaled

/-!
# Exit-time lower tail: from the walk event to the Brownian event

Three steps of the proof of [BG20, Lemma 6.9], between the event `(6.28)` for the walk on the mated-CRT map and
the Brownian estimate `(6.29)`:

* `exists_lt_stepTime_stopped_walk`: on the cell-size event, if the walk started at `x` leaves the cells of
  `B_δ(η(εx))` before its `K`-th successive exit from the cells of balls of radius `q`, then the interpolated walk
  stopped at its exit from `B_R(0)` moves by `δ` from its starting point strictly before its `K`-th displacement
  time of size `2q + 6c`;
* `exists_le_stepTime_of_cmpEDist_lt`: if a planar path stopped at its exit from `U` is within distance `κ`, modulo
  time parametrization, of a path with such a displacement, then the (unstopped) planar path moves by `a - 2κ` from
  its starting point no later than its `K`-th displacement time of size `r`, whenever `2s + 2κ ≤ r`;
* `srwLaw_le_planarBrownianMotion_add`: the per-environment step: on the cell-size event, the adjacency event and
  the event of the uniform-start invariance principle, the walk probability of `(6.28)` is at most the Brownian
  probability of the displacement event plus `κ`;
* `planarBrownianMotion_exit_by_stepTime_superpoly`: [BG20, (6.29)] for planar Brownian motion started at `z`,
  with a constant uniform in `z` and in the scale `a`.
-/

open Set Metric MeasureTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.ExitTailCombine

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **The walk event gives a displacement before the `K`-th step of the stopped interpolated walk.** On the
cell-size event in `B_R(0)`, for a walk `w` with adjacent cells and `‖η(ε w_0)‖ + δ + 5c < R`: if `w` leaves the
cells of `B_δ(η(ε w_0))` before its `K`-th successive exit `σ_K` from the cells of the balls of radius `q`, then the
interpolated walk stopped at its exit from `B_R(0)` reaches distance `δ` from its starting point strictly before its
`K`-th displacement time of size `2q + 6c`. -/
theorem exists_lt_stepTime_stopped_walk (hε : 0 ≤ ε) (hη : Continuous η) {R c δ q : ℝ} (hδ : 0 < δ)
    (hc : 0 ≤ c) (hq : 0 < q) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {K : ℕ}
    (hK : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w <
      SuccessiveExitGaps.succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) K w) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) <
        LatticeProb.stepTime (stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w)) (2 * q + 6 * c) K ∧
      δ ≤ ‖stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) t -
        stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) 0‖ := by
  set A : ℤ → Set ℤ := fun z => cellVertices ε η (ball (vertexPoint ε η z) q) with hA
  obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hK)
  have hτ := LatticeProb.le_stepTime_of_block_norm_sub_lt
    (f := stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w)) (r := 2 * q + 6 * c)
    (τ := fun k => ((WalkDisplacementBlocks.truncExit A w (n₀ + 1) k : ℕ) : ℝ≥0∞))
    (WalkDisplacementBlocks.coe_truncExit_zero A w (n₀ + 1))
    (WalkDisplacementBlocks.norm_sub_lt_on_block hε hη hδ hc hq hcell hadj hconf hn₀.symm) K
  have hlt : (n₀ : ℕ∞) < SuccessiveExitGaps.succExit A K w := hn₀ ▸ hK
  simp only [WalkDisplacementBlocks.truncExit_of_lt A w hlt] at hτ
  refine ⟨(n₀ : ℝ≥0), ?_,
    WalkDisplacementBlocks.le_norm_stopAtExit_sub hε hη hδ hc hcell hadj hconf hn₀.symm⟩
  refine lt_of_lt_of_le ?_ hτ
  rw [ENNReal.coe_natCast]
  exact_mod_cast Nat.lt_succ_self n₀

/-- **Transfer of the displacement event to a planar path, in both exit cases.** If the path `b` stopped at its
exit from `U` is within distance `κ` of `f` modulo time parametrization, and `f` reaches distance `a` from `f 0`
strictly before its `K`-th displacement time of size `s`, then `b` reaches distance `a - 2κ` from `b 0` no later
than its `K`-th displacement time of size `r`, whenever `2s + 2κ ≤ r`. -/
theorem exists_le_stepTime_of_cmpEDist_lt {U : Set ℂ} {f b : ℝ≥0 → ℂ} {κ s r a : ℝ}
    (h : cmpEDist (stopAtExit U b) f < ENNReal.ofReal κ) (hr : 2 * s + 2 * κ ≤ r) {K : ℕ}
    (hf : ∃ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f s K ∧ a ≤ ‖f t - f 0‖) :
    ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ LatticeProb.stepTime b r K ∧ a - 2 * κ ≤ ‖b u - b 0‖ := by
  by_cases hexit : pathExitTime U b = ⊤
  · obtain ⟨u, hu, ha⟩ :=
      CmpEDistPointwise.exists_lt_stepTime_of_cmpEDist_lt_of_exit_eq_top hexit h hr hf
    exact ⟨u, hu.le, ha⟩
  · obtain ⟨ψ, hψ⟩ := CmpEDistPointwise.exists_orderIso_norm_sub_stopped_le_of_cmpEDist_lt hexit h
    obtain ⟨u, hu, -, ha⟩ := LatticeProb.exists_le_stepTime_of_norm_sub_comp_stopped_le ψ hψ hr hf
    exact ⟨u, hu, ha⟩

/-- The simple random walk starts at its starting point almost surely. -/
theorem ae_srwLaw_eval_zero (m : ℤ → ℤ → ℕ) (x : ℤ) : ∀ᵐ w ∂srwLaw m x, w 0 = x := by
  have hms : MeasurableSet {w : ℕ → ℤ | w 0 = x} :=
    show MeasurableSet ((fun w : ℕ → ℤ => w 0) ⁻¹' {x}) from
      (measurable_pi_apply 0) (measurableSet_singleton x)
  have h1 : srwLaw m x {w | w 0 = x} = 1 := by
    simpa using FirstPass.Derived.srwLaw_eval_zero m x x
  rw [ae_iff]
  change srwLaw m x {w | w 0 = x}ᶜ = 0
  rw [measure_compl hms (measure_ne_top _ _), h1, measure_univ, tsub_self]

/-- **The per-environment step of [BG20, Lemma 6.9].** Fix an environment `(ε, η, m)` on the cell-size event in
`B_R(0)` (cell diameters at most `c`), on the adjacency event (successive cells of the walk meet) and on the event
of the uniform-start invariance principle with tolerance `κ`, and let `ρ + δ + 5c < R`. For a vertex `x` whose cell
meets `B_{ρ-δ}(0)`, the probability that the walk from `x` leaves the cells of `B_δ(η(εx))` before its `K`-th
successive exit from the cells of balls of radius `q` is at most `κ` plus the probability that planar Brownian
motion from `η(εx)` moves by `a` no later than its `K'`-th displacement time of size `r`, whenever `a ≤ δ - 2κ`,
`2(2q + 6c) + 2κ ≤ r` and `K ≤ K'`. -/
theorem srwLaw_le_planarBrownianMotion_add (hε : 0 ≤ ε) (hη : Continuous η) {m : ℤ → ℤ → ℕ}
    {R ρ c δ q κ a r : ℝ} {K K' : ℕ} (hδ : 0 < δ) (hc : 0 ≤ c) (hq : 0 < q) (hcδ : c ≤ δ)
    (hρR : ρ - δ ≤ R) (hconf : ρ + δ + 5 * c < R)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    (hadj : ∀ y : ℤ, ∀ᵐ w ∂srwLaw m y, ∀ n, (cell ε η (w n) ∩ cell ε η (w (n + 1))).Nonempty)
    (hN4 : ∀ x : ℤ, vertexPoint ε η x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw m x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) ∈ A} ≤
        planarBrownianMotion (vertexPoint ε η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
          ENNReal.ofReal κ)
    (ha : a ≤ δ - 2 * κ) (hr : 2 * (2 * q + 6 * c) + 2 * κ ≤ r) (hK : K ≤ K')
    {x : ℤ} (hx : x ∈ cellVertices ε η (ball 0 (ρ - δ))) :
    srwLaw m x {w | vExitTime (cellVertices ε η (ball (vertexPoint ε η x) δ)) w <
        SuccessiveExitGaps.succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) K w} ≤
      planarBrownianMotion (vertexPoint ε η x)
          {b | ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ LatticeProb.stepTime (⇑b) r K' ∧ a ≤ ‖b u - b 0‖} +
        ENNReal.ofReal κ := by
  have hv := ExitTailAssembly.vertexPoint_mem_closedBall_of_mem_cellVertices hη hε hx hρR hcell hcδ
  have hvρ : ‖vertexPoint ε η x‖ ≤ ρ := mem_closedBall_zero_iff.mp hv
  set A : Set (ℝ≥0 → ℂ) := {f | ∃ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f (2 * q + 6 * c) K ∧
    δ ≤ ‖f t - f 0‖} with hA
  calc _ ≤ srwLaw m x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) ∈ A} := by
        refine measure_mono_ae ?_
        filter_upwards [hadj x, ae_srwLaw_eval_zero m x] with w hw hw0 hbad
        have hbad' : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w <
            SuccessiveExitGaps.succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) K w := by
          rw [hw0]; exact hbad
        exact exists_lt_stepTime_stopped_walk hε hη hδ hc hq hcell hw (by rw [hw0]; linarith) hbad'
    _ ≤ _ := hN4 x hv A
    _ ≤ _ := by
        refine add_le_add (measure_mono (μ := planarBrownianMotion (vertexPoint ε η x)) fun b hb => ?_) le_rfl
        obtain ⟨f, hfA, hf⟩ := hb
        obtain ⟨u, hu, hau⟩ := exists_le_stepTime_of_cmpEDist_lt hf hr hfA
        exact ⟨u, hu.trans (LatticeProb.monotone_stepTime hK), ha.trans hau⟩

/-- Displacement times depend only on the increments `‖f t - f s‖`. -/
theorem stepTime_eq_of_norm_sub_eq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ≥0 → E} {g : ℝ≥0 → F} (h : ∀ s t, ‖f t - f s‖ = ‖g t - g s‖) (r : ℝ) (k : ℕ) :
    LatticeProb.stepTime f r k = LatticeProb.stepTime g r k := by
  have hset : ∀ a, LatticeProb.stepSet f r a = LatticeProb.stepSet g r a := fun a => by
    unfold LatticeProb.stepSet
    simp_rw [h]
  have hnext : ∀ a, LatticeProb.nextStep f r a = LatticeProb.nextStep g r a := fun a => by
    rw [LatticeProb.nextStep, LatticeProb.nextStep, hset a]
  induction k with
  | zero => rfl
  | succ k ih => simp only [LatticeProb.stepTime, ih, hnext]

/-- **[BG20, (6.29)] for planar Brownian motion.** For `0 < ζ < 1` and `p ∈ ℕ` there is `C` such that for every
starting point `z`, every scale `a > 0` and every `0 < r < 1`, planar Brownian motion started at `z` reaches distance
`a` from `z` no later than its `K`-th displacement time of size `a r`, `K = ⌊r ^ -(2 - ζ)⌋`, with probability at
most `C r ^ p`. -/
theorem planarBrownianMotion_exit_by_stepTime_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (a : ℝ≥0), 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      planarBrownianMotion z {b | ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤
          LatticeProb.stepTime (⇑b) ((a : ℝ) * r) ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ ∧ (a : ℝ) ≤ ‖b u - b 0‖}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := LatticeProb.measure_exit_by_stepTime_superpoly_scaled.{0} 2 two_pos hζ0 hζ1 p
  refine ⟨C, fun z a ha r hr0 hr1 => ?_⟩
  have hB := PlanarBrownianSpace.isBrownianSpace_halfSpeedPath z
  refine le_trans (measure_mono_ae ?_) (hC _ (planarBrownianMotion z) _ hB a ha r hr0 hr1)
  filter_upwards [hB.start] with b hb hbS
  obtain ⟨u, hu, hau⟩ := hbS
  have hb0 : b 0 = z := by
    have h0 : PlanarBrownianSpace.halfSpeedPath z 0 b = 0 := hb
    rw [PlanarBrownianSpace.halfSpeedPath, mul_zero, LinearIsometryEquiv.map_eq_zero_iff,
      sub_eq_zero] at h0
    exact h0
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (2⁻¹ : ℝ≥0) (by norm_num)
  have hφ : ∀ t, φ t = 2⁻¹ * t := fun _ => rfl
  have hcongr : ∀ k, LatticeProb.stepTime (fun t => PlanarBrownianSpace.halfSpeedPath z t b)
      ((a : ℝ) * r) k = LatticeProb.stepTime (⇑b ∘ φ) ((a : ℝ) * r) k :=
    stepTime_eq_of_norm_sub_eq (fun s t => by
      simp only [PlanarBrownianSpace.halfSpeedPath, Function.comp_apply, hφ, ← map_sub,
        LinearIsometryEquiv.norm_map, sub_sub_sub_cancel_right]) _
  refine ⟨2 * u, ?_, ?_⟩
  · rw [hcongr, LatticeProb.coe_le_stepTime_comp_iff, hφ, ← mul_assoc, inv_mul_cancel₀ two_ne_zero,
      one_mul]
    exact hu
  · rw [PlanarBrownianSpace.norm_halfSpeedPath, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul, ← hb0]
    exact hau

end MatedCRT.ExitTailCombine
