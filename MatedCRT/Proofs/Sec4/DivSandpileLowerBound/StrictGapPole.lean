import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapStrongMinimum
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Steps.Sec11.OdometerMaximum
import HarmonicBalls.Proofs.Sec5.CompactClusterMeasureLocality

/-! Positivity of the odometer increment near the pole. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter _root_.HarmonicBalls
open scoped Topology

/-- The Green singularity forces the odometer increment to be positive at
some point of every open neighbourhood of the pole. -/
theorem exists_pos_odometer_increment_near_pole
    {μ : Measure ℂ} {ρ s t : ℝ} {z : ℂ} (hz : z ∈ ball 0 ρ) (hst : s < t)
    (hws : ContinuousOn (leastSupersolution μ ρ z s) (closedBall 0 ρ))
    (hwt : ContinuousOn (leastSupersolution μ ρ z t) (closedBall 0 ρ))
    {U : Set ℂ} (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ x ∈ U \ {z}, 0 < odometer μ ρ z t x - odometer μ ρ z s x := by
  have hnear : closedBall (0 : ℂ) ρ ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hdiff : ContinuousAt (fun x => leastSupersolution μ ρ z t x -
      leastSupersolution μ ρ z s x) z :=
    (hwt.continuousAt hnear).sub (hws.continuousAt hnear)
  let d := leastSupersolution μ ρ z t z - leastSupersolution μ ρ z s z
  have hbound : ∀ᶠ x in 𝓝[≠] z,
      d - 1 < leastSupersolution μ ρ z t x - leastSupersolution μ ρ z s x :=
    eventually_nhdsWithin_of_eventually_nhds
      (hdiff.eventually (Ioi_mem_nhds (show d - 1 < d by linarith)))
  have hgreen : ∀ᶠ x in 𝓝[≠] z,
      (1 - d) / (t - s) < greenFunction (ball 0 ρ) z x :=
    (tendsto_greenFunction_ball_pole hz).eventually (eventually_gt_atTop _)
  have hUev : ∀ᶠ x in 𝓝[≠] z, x ∈ U :=
    eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hzU)
  have hex : ∀ᶠ x in 𝓝[≠] z, x ∈ U \ {z} ∧
      0 < odometer μ ρ z t x - odometer μ ρ z s x := by
    filter_upwards [hbound, hgreen, hUev, self_mem_nhdsWithin] with x hb hg hx hne
    refine ⟨⟨hx, hne⟩, ?_⟩
    have hg' := (div_lt_iff₀ (sub_pos.mpr hst)).mp hg
    dsimp only [odometer]
    dsimp only [d] at hb hg'
    nlinarith
  exact hex.exists

/-- For a compactly confined cluster, odometer regularity and pole divergence
reduce strict comparison to superharmonicity of the increment. -/
theorem regularized_cluster_subset_later_cluster_of_superharmonicity
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hopen : IsOpen (cluster μ ρ z s))
    (hconn : IsPreconnected (cluster μ ρ z s))
    (hcompact : closure (cluster μ ρ z s) ⊆ ball 0 ρ)
    (hsuper : IsSuperharmonicOn (interior (closure (cluster μ ρ z s)) \ {z})
      (fun x => odometer μ ρ z t x - odometer μ ρ z s x)) :
    interior (closure (cluster μ ρ z s)) ⊆ cluster μ ρ z t := by
  have hsub : interior (closure (cluster μ ρ z s)) \ {z} ⊆ ball (0 : ℂ) ρ \ {z} :=
    fun x hx => ⟨hcompact (interior_subset hx.1), hx.2⟩
  have hc := ((odometer_continuousOn_and_subharmonic hμ hρ hV hz (hs.trans hst)).1.sub
    (odometer_continuousOn_and_subharmonic hμ hρ hV hz hs).1).mono hsub
  obtain ⟨_, _, hws⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hρ hV hz hs
  obtain ⟨_, _, hwt⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hρ hV hz (hs.trans hst)
  have hzreg : z ∈ interior (closure (cluster μ ρ z s)) :=
    hopen.subset_interior_closure (self_mem_cluster hz)
  have hpos := exists_pos_odometer_increment_near_pole hz hst hws.1 hwt.1
    isOpen_interior hzreg
  exact regularized_cluster_subset_later_cluster_of_superharmonic_increment
    hμ hρ hV hz hs hst hopen hconn hcompact hc hsuper hpos

end MatedCRT
