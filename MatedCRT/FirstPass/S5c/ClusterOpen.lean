import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S1c.Cluster
import MatedCRT.FirstPass.Frozen.S5c

/-!
# FIRST PASS, Lemma 5.3 (three-inputs section 3, A5/A1 prerequisite): openness of the stopped cluster

The obstacle cluster `cluster μ ρ 0 t = {x ∈ B_ρ | x = 0 ∨ -t G_{B_ρ}(0,x) < v(x)}` (Harmonic-Balls-LQG
Defs/Obstacle.lean:69) is open whenever the least supersolution `v` is continuous on the closed disc and the disc Green
function is continuous off the pole and blows up at the pole (Armitage-Gardiner). `isOpen_cluster_diff_pole`
(FirstPass/S1c/Cluster.lean) gives openness off the pole; here the pole is handled by `FPGreenBallPoleLimit`.

For a cone harmonic-ball family the continuity of `v` on `B̄_ρ` is part of `SatisfiesObstacleCharacterization`, and
it holds at radius `ρ` as soon as `Λ_t ⊆ B_r` for some `r < ρ`. For `t < clusterExitTime Λ ρ` (sup of
`{s > 0 | Λ_s ⊆ B_{ρ/3}}`) such an `r = ρ/3` exists, by monotonicity of `Λ` (`SatisfiesHarmonicBallConditions.monotoneOn`).
Hence the cluster is open on the stopped event, almost surely. No new frozen input beyond the two disc Green facts.
-/

open HarmonicBalls MeasureTheory Filter Topology Set Metric

namespace MatedCRT

/-- The obstacle cluster of radius `ρ` at mass `u > 0` is open when the least supersolution is continuous on the closed
disc, the disc Green function is continuous off the pole and blows up there. -/
theorem isOpen_cluster_of_pole (μ : Measure ℂ) {ρ u : ℝ} (hρ : 0 < ρ) (hu : 0 < u)
    (hv : ContinuousOn (leastSupersolution μ ρ 0 u) (closedBall 0 ρ))
    (hG : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0}))
    (hpole : Tendsto (greenFunction (ball 0 ρ) 0) (nhdsWithin (0 : ℂ) {0}ᶜ) atTop) :
    IsOpen (cluster μ ρ 0 u) := by
  have hdiff : IsOpen (cluster μ ρ 0 u \ {0}) := isOpen_cluster_diff_pole μ hv hG
  have hvlim : Tendsto (leastSupersolution μ ρ 0 u) (nhdsWithin (0 : ℂ) {0}ᶜ)
      (nhds (leastSupersolution μ ρ 0 u 0)) :=
    ((hv.continuousAt (closedBall_mem_nhds (0 : ℂ) hρ)).tendsto).mono_left nhdsWithin_le_nhds
  have hGlim : Tendsto (fun x => u * greenFunction (ball 0 ρ) 0 x) (nhdsWithin (0 : ℂ) {0}ᶜ) atTop :=
    hpole.const_mul_atTop hu
  have hsum := (hGlim.atTop_add hvlim).eventually_gt_atTop 0
  have hnhd : ∀ᶠ x in nhds (0 : ℂ), x ∈ cluster μ ρ 0 u := by
    filter_upwards [eventually_nhdsWithin_iff.1 hsum, isOpen_ball.mem_nhds (mem_ball_self hρ)] with x hx hxB
    by_cases h0 : x = 0
    · subst h0
      exact ⟨hxB, Or.inl rfl⟩
    · have hpos := hx h0
      exact ⟨hxB, Or.inr (by linarith)⟩
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  by_cases h0 : x = 0
  · subst h0
    exact hnhd
  · exact Filter.mem_of_superset (hdiff.mem_nhds ⟨hx, h0⟩) sdiff_subset

/-- Openness of the cluster for a cone harmonic-ball family, from `Λ_t ⊆ B_r` with `r < ρ`, given the two disc Green
facts (`FPGreenBallContinuousOffPole`, `FPGreenBallPoleLimit`). -/
theorem isOpen_cluster_of_family (hG0 : MatedCRT.FPGreenBallContinuousOffPole)
    (hp : MatedCRT.FPGreenBallPoleLimit) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hΛ : Λ t ⊆ ball 0 r)
    (hrρ : r < ρ) : IsOpen (cluster μ ρ 0 t) := by
  have hρ : 0 < ρ := lt_trans hr hrρ
  obtain ⟨_, _, hobs⟩ := hfam
  obtain ⟨_, hv, _, _⟩ := hobs t r ht hr hΛ ρ hrρ
  have hG : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0}) := hG0 ρ hρ
  exact isOpen_cluster_of_pole μ hρ ht hv hG (hp ρ hρ)

/-- On the stopped event `{t < clusterExitTime Λ ρ}` the cluster `cluster μ ρ 0 t` is open (monotonicity of `Λ`
gives `Λ_t ⊆ Λ_s ⊆ B_{ρ/3}` for some `s > t` with `Λ_s ⊆ B_{ρ/3}`). -/
theorem isOpen_cluster_of_stopped (hG0 : MatedCRT.FPGreenBallContinuousOffPole)
    (hp : MatedCRT.FPGreenBallPoleLimit) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) : IsOpen (cluster μ ρ 0 t) := by
  have hne : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    unfold clusterExitTime at hT
    rw [h, Real.sSup_empty] at hT
    linarith
  obtain ⟨s, ⟨hs, hsB⟩, hts⟩ := exists_lt_of_lt_csSup hne hT
  have hmono : Λ t ≤ Λ s := hfam.2.1.monotoneOn ht hs hts.le
  have hsub : Λ t ⊆ ball 0 (ρ / 3) := fun x hx => hsB (hmono hx)
  exact isOpen_cluster_of_family hG0 hp hfam ht (by linarith) hsub (by linarith)

/-- Almost surely, the stopped cluster is open: for a random cone harmonic-ball family, `ω ↦ cluster (μ ω) ρ 0 t` is
open on `{t < clusterExitTime (Λ ω) ρ}`. -/
theorem ae_isOpen_cluster_of_stopped {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (hG0 : MatedCRT.FPGreenBallContinuousOffPole) (hp : MatedCRT.FPGreenBallPoleLimit)
    (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ) (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∀ᵐ ω ∂P, t < clusterExitTime (Λ ω) ρ → IsOpen (cluster (μ ω) ρ 0 t) :=
  hfam.mono fun _ hω hT => isOpen_cluster_of_stopped hG0 hp hω hρ ht hT

end MatedCRT
