import HarmonicBalls.Proofs.Sec9.StrongMinimum
import HarmonicBalls.Proofs.Sec10.CountableDeletionCrossings
import HarmonicBalls.Proofs.Sec5.OdometerTimeContinuity

/-! Strong minimum principle on a preconnected planar domain. -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- A continuous nonnegative superharmonic function on a preconnected open
set is strictly positive everywhere if it is positive at one point. -/
theorem IsSuperharmonicOn.pos_of_nonneg_of_exists_pos
    {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hc : ContinuousOn u U) (hs : IsSuperharmonicOn U u)
    (hnonneg : ∀ x ∈ U, 0 ≤ u x) (hpos : ∃ x ∈ U, 0 < u x) :
    ∀ x ∈ U, 0 < u x := by
  let Z : Set ℂ := {x | x ∈ U ∧ u x = 0}
  let V : Set ℂ := U ∩ u ⁻¹' Ioi 0
  have hZo : IsOpen Z := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨r, hr, hsub, hzero⟩ := hs.exists_ball_eq_zero hU hc hnonneg hx.1 hx.2
    refine ⟨r, hr, ?_⟩
    intro y hy
    exact ⟨hsub hy, hzero hy⟩
  have hVo : IsOpen V := hc.isOpen_inter_preimage hU isOpen_Ioi
  have hdis : Disjoint Z V := by
    apply disjoint_left.mpr
    intro x hxZ hxV
    exact (ne_of_gt hxV.2) hxZ.2
  have hcover : U ⊆ Z ∪ V := by
    intro x hx
    rcases (hnonneg x hx).eq_or_lt with hzero | hpositive
    · exact Or.inl ⟨hx, hzero.symm⟩
    · exact Or.inr ⟨hx, hpositive⟩
  have hVne : (U ∩ V).Nonempty := by
    obtain ⟨x, hx, hp⟩ := hpos
    exact ⟨x, hx, hx, hp⟩
  have hsub := hconn.subset_right_of_subset_union hZo hVo hdis hcover hVne
  intro x hx
  exact (hsub hx).2

/-- The strong minimum principle applies on the punctured regularization of
a preconnected open planar set. -/
theorem IsSuperharmonicOn.pos_on_punctured_regularization
    {C : Set ℂ} {z : ℂ} {u : ℂ → ℝ}
    (hC : IsOpen C) (hconn : IsPreconnected C)
    (hc : ContinuousOn u (interior (closure C) \ {z}))
    (hs : IsSuperharmonicOn (interior (closure C) \ {z}) u)
    (hnonneg : ∀ x ∈ interior (closure C) \ {z}, 0 ≤ u x)
    (hpos : ∃ x ∈ interior (closure C) \ {z}, 0 < u x) :
    ∀ x ∈ interior (closure C) \ {z}, 0 < u x := by
  have hreg : IsPreconnected (interior (closure C)) :=
    hconn.subset_closure hC.subset_interior_closure interior_subset
  have hpunct : IsPreconnected (interior (closure C) \ {z}) :=
    isPreconnected_sdiff_countable_of_isOpen isOpen_interior hreg
      ((countable_singleton z).mono inter_subset_left)
  exact IsSuperharmonicOn.pos_of_nonneg_of_exists_pos
    (isOpen_interior.sdiff isClosed_singleton) hpunct hc hs hnonneg hpos

/-- Comparison of a regularized cluster with a later raw cluster, once the
odometer increment is superharmonic and positive somewhere on the punctured
regularization. -/
theorem regularized_cluster_subset_later_cluster_of_superharmonic_increment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hopen : IsOpen (cluster μ ρ z s))
    (hconn : IsPreconnected (cluster μ ρ z s))
    (hcompact : closure (cluster μ ρ z s) ⊆ ball 0 ρ)
    (hc : ContinuousOn (fun x => odometer μ ρ z t x - odometer μ ρ z s x)
      (interior (closure (cluster μ ρ z s)) \ {z}))
    (hsuper : IsSuperharmonicOn (interior (closure (cluster μ ρ z s)) \ {z})
      (fun x => odometer μ ρ z t x - odometer μ ρ z s x))
    (hpos : ∃ x ∈ interior (closure (cluster μ ρ z s)) \ {z},
      0 < odometer μ ρ z t x - odometer μ ρ z s x) :
    interior (closure (cluster μ ρ z s)) ⊆ cluster μ ρ z t := by
  have hsub : interior (closure (cluster μ ρ z s)) ⊆ ball (0 : ℂ) ρ :=
    interior_subset.trans hcompact
  have hnonneg : ∀ x ∈ interior (closure (cluster μ ρ z s)) \ {z},
      0 ≤ odometer μ ρ z t x - odometer μ ρ z s x := by
    intro x hx
    exact (odometer_time_increment_bounds hμ hρ hV hz (ball_subset_closedBall (hsub hx.1))
      (by simpa using hx.2) hs hst.le).1
  have hstrict := IsSuperharmonicOn.pos_on_punctured_regularization hopen hconn hc hsuper hnonneg hpos
  intro x hx
  apply mem_cluster_iff.mpr
  refine ⟨hsub hx, ?_⟩
  by_cases hxz : x = z
  · exact Or.inl hxz
  · right
    have hinc := hstrict x ⟨hx, by simpa using hxz⟩
    have hnon := odometer_nonneg (μ := μ) hs.le (ball_subset_closedBall (hsub hx)) hxz
    linarith

end MatedCRT
