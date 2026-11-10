import MatedCRT.FirstPass.S5k.Uniqueness
import MatedCRT.FirstPass.Frozen.S2g
import MatedCRT.FirstPass.Frozen.S5k

/-!
# First pass: the continuum least supersolution solves (6) (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Identification step (7) of Part I, Step 4.2 of `notes/fp-gaps/CHATGPT-z5-floor.md`: for `0 < t < clusterExitTime Λ ρ`
the continuum least supersolution `W_t = leastSupersolution μ ρ 0 t` solves (6) of Step 4.1 for the measure `μ|_{B̄_ρ}`
(`IsObstacleSolutionOn`). Inputs: the obstacle characterization of the harmonic-ball family (`IsConeHarmonicBallFamily`,
Setting.lean), the supersolution membership of `W_t` (`FrozenLeastSupersolutionMemCone`, `Frozen/S5k.lean`) and the disc
Green function (`FrozenGreenDiscPole`, `Frozen/S2g.lean`), used for the openness of the cluster `U_W`.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology
open HarmonicBalls Laplacian

/-- Integrals of a function supported in `S ⊆ A` against `μ.restrict A` and against `μ` agree. -/
theorem integral_restrict_eq_of_tsupport {μ : Measure ℂ} {A S : Set ℂ} {φ : ℂ → ℝ}
    (hS : tsupport φ ⊆ S) (hSA : S ⊆ A) : ∫ x, φ x ∂(μ.restrict A) = ∫ x, φ x ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hSA (hS h)))

/-- A function whose support lies in `A` is `μ.restrict A`-integrable iff it is `μ`-integrable. -/
theorem integrable_restrict_iff_of_tsupport {μ : Measure ℂ} {A : Set ℂ} {φ : ℂ → ℝ} (hA : tsupport φ ⊆ A) :
    Integrable φ (μ.restrict A) ↔ Integrable φ μ :=
  integrableOn_iff_integrable_of_support_subset ((subset_tsupport φ).trans hA)

/-- The cluster `U_w` of a function continuous on `B̄_ρ` is open (pole `0`, `t > 0`): away from the pole this is the
openness of `{w + tG > 0}`, and at the pole `G(0,·) → +∞` (`FrozenGreenDiscPole`) while `w` is bounded below. -/
theorem isOpen_obstacleCluster (hG : FrozenGreenDiscPole) {ρ t : ℝ} {w : ℂ → ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hw : ContinuousOn w (closedBall (0 : ℂ) ρ)) : IsOpen (floorObstacleCluster ρ t w) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxb, hx⟩
  by_cases hx0 : x = 0
  · subst hx0
    have hGt : Tendsto (greenFunction (ball 0 ρ) 0) (𝓝[≠] (0 : ℂ)) atTop := ((hG ρ hρ).2)
    have hwc : ContinuousAt w 0 := hw.continuousAt (closedBall_mem_nhds 0 hρ)
    have hw1 : ∀ᶠ y in 𝓝 (0 : ℂ), w 0 - 1 < w y :=
      hwc.tendsto.eventually (lt_mem_nhds (show w 0 - 1 < w 0 by linarith))
    have hG1 : ∀ᶠ y in 𝓝[≠] (0 : ℂ), (1 - w 0) / t < greenFunction (ball 0 ρ) 0 y :=
      hGt.eventually_gt_atTop _
    have hballP : ∀ᶠ y in 𝓝[≠] (0 : ℂ), y ∈ ball (0 : ℂ) ρ :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))
    have hpunct : ∀ᶠ y in 𝓝[≠] (0 : ℂ), y ∈ floorObstacleCluster ρ t w := by
      filter_upwards [hG1, nhdsWithin_le_nhds hw1, hballP] with y hG1y hw1y hby
      refine mem_obstacleCluster.2 ⟨hby, Or.inr ?_⟩
      have h2 : 1 - w 0 < greenFunction (ball 0 ρ) 0 y * t := (div_lt_iff₀ ht).mp hG1y
      nlinarith
    have hev : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ floorObstacleCluster ρ t w := by
      filter_upwards [eventually_nhdsWithin_iff.mp hpunct] with y hy
      by_cases hy0 : y = 0
      · subst hy0
        exact mem_obstacleCluster.2 ⟨mem_ball_self hρ, Or.inl rfl⟩
      · exact hy hy0
    exact hev
  · have hopen : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball (0 : ℂ) ρ \ {0}) :=
      (hG ρ hρ).1.mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have hwc : ContinuousOn w (ball (0 : ℂ) ρ \ {0}) := hw.mono (sdiff_subset.trans ball_subset_closedBall)
    have hfc : ContinuousOn (fun y => w y + t * greenFunction (ball 0 ρ) 0 y) (ball (0 : ℂ) ρ \ {0}) :=
      hwc.add (continuousOn_const.mul hGc)
    have hO := hfc.isOpen_inter_preimage hopen (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))
    have hxO : x ∈ ball (0 : ℂ) ρ \ {0} ∩ (fun y => w y + t * greenFunction (ball 0 ρ) 0 y) ⁻¹' Ioi 0 := by
      refine ⟨⟨hxb, hx0⟩, ?_⟩
      have := (mem_obstacleCluster.1 (show x ∈ floorObstacleCluster ρ t w from ⟨hxb, hx⟩)).2
      rcases this with h | h
      · exact absurd h hx0
      · show 0 < w x + t * greenFunction (ball 0 ρ) 0 x
        nlinarith
    refine Filter.mem_of_superset (hO.mem_nhds hxO) ?_
    rintro y ⟨⟨hyb, hy0⟩, hy⟩
    refine mem_obstacleCluster.2 ⟨hyb, Or.inr ?_⟩
    show -t * greenFunction (ball 0 ρ) 0 y < w y
    have hy' : 0 < w y + t * greenFunction (ball 0 ρ) 0 y := hy
    nlinarith

/-- Exit-time lemma: for `0 < t < clusterExitTime Λ ρ` there is `s > t` with `Λ_s ⊆ B_{ρ/3}` (the supremum defining
`clusterExitTime` is over a set of times with `Λ_s ⊆ B_{ρ/3}`). -/
theorem exists_gt_subset_of_lt_clusterExitTime {Λ : ℝ → Set ℂ} {ρ t : ℝ} (ht : 0 < t)
    (hexit : t < clusterExitTime Λ ρ) : ∃ s, t < s ∧ 0 < s ∧ Λ s ⊆ ball (0 : ℂ) (ρ / 3) := by
  unfold clusterExitTime at hexit
  by_cases hb : BddAbove {s : ℝ | 0 < s ∧ Λ s ⊆ ball (0 : ℂ) (ρ / 3)}
  · by_cases hne : ({s : ℝ | 0 < s ∧ Λ s ⊆ ball (0 : ℂ) (ρ / 3)}).Nonempty
    · obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne hexit
      exact ⟨s, hts, hs.1, hs.2⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sSup_empty] at hexit
      linarith
  · rw [Real.sSup_of_not_bddAbove hb] at hexit
    linarith

/-- **Identification (7).** For `0 < t < clusterExitTime Λ ρ`, the continuum least supersolution solves (6) for the
restriction of `μ` to `B̄_ρ`, given the supersolution membership of `W_t` (`hsup`). -/
theorem isObstacleSolutionOn_leastSupersolution (hG : FrozenGreenDiscPole) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hsup : leastSupersolution μ ρ 0 t ∈ supersolutions μ ρ 0 t) (hexit : t < clusterExitTime Λ ρ) :
    IsObstacleSolutionOn ρ t (μ.restrict (closedBall (0 : ℂ) ρ)) (leastSupersolution μ ρ 0 t) := by
  obtain ⟨s, hts, hs, hsub⟩ := exists_gt_subset_of_lt_clusterExitTime ht hexit
  have hΛt : Λ t ⊆ ball (0 : ℂ) (ρ / 3) :=
    Set.Subset.trans (hΛ.2.1.monotoneOn ht hs hts.le) hsub
  obtain ⟨hLam, hcont, hLap, hzero⟩ := hΛ.2.2 t (ρ / 3) ht (by linarith) hΛt ρ (by linarith)
  have hUopen : IsOpen (floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t)) :=
    isOpen_obstacleCluster hG hρ ht hcont
  have hUball : floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t) ⊆ ball (0 : ℂ) ρ :=
    fun x hx => (mem_obstacleCluster.1 hx).1
  have hUsub : floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t) ⊆ Λ t := by
    rw [hLam]
    exact hUopen.subset_interior_iff.mpr subset_closure
  obtain ⟨-, hLE, -⟩ := hsup
  refine ⟨hcont, hzero, fun x hx hx0 => le_leastSupersolution ht.le hx hx0, ?_, ?_⟩
  · refine ⟨hLE.1, fun φ hφ hφ0 hint => ?_⟩
    have hφμ : Integrable φ μ :=
      (integrable_restrict_iff_of_tsupport (hφ.2.2.trans ball_subset_closedBall)).1 hint
    have hle := hLE.2 φ hφ hφ0 hφμ
    rw [integral_restrict_eq_of_tsupport hφ.2.2 ball_subset_closedBall]
    exact hle
  · refine ⟨hLap.1.mono_set hUball, fun φ hφ => ?_⟩
    have hφb : IsTestFunction (ball (0 : ℂ) ρ) φ := isTestFunction_of_subset hφ hUball
    have hφΛ : tsupport φ ⊆ Λ t := hφ.2.2.trans hUsub
    obtain ⟨hI1, -, heq⟩ := hLap.2 φ hφb
    have hφμ : Integrable φ μ := (integrable_restrict_iff_of_tsupport hφΛ).1 hI1
    refine ⟨hφμ.restrict, integrable_zero_measure, ?_⟩
    rw [heq, integral_zero_measure, sub_zero,
      integral_restrict_eq_of_tsupport (A := Λ t) (S := Λ t) hφΛ subset_rfl,
      integral_restrict_eq_of_tsupport (hφ.2.2.trans hUball) ball_subset_closedBall, sub_zero]

end MatedCRT
