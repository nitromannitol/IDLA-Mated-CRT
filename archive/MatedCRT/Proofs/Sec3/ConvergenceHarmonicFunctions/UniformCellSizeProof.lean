import MatedCRT.Steps.Sec3.UniformCellSize
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSegmentsContainBalls

/-!
# Deterministic geometry for the uniform cell-size estimate

The first-exit argument below adapts Leonardo Bonanno's
`MatedCRTHarmonic.GMSLemma27.diam_segment_le_of_balls` to an arbitrary
intermediate radius and uses only the mass of the whole cell. It is the
geometric part of steps2.tex, lines 186–229.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT.Sec3

/-- The segment-ball event is invariant under an increasing time change. -/
theorem segment_balls_of_reparametrization (L : C(ℝ, ℂ)) (η : ℝ → ℂ)
    (v : ℝ ≃o ℝ) (hη : ∀ t, η t = L (v t)) {R r δ : ℝ}
    (hδ : 0 < δ) (hseg : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls L R r δ) :
    ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball 0 R →
      δ ^ (1 - r) ≤ diam (η '' Icc a b) → ∃ w : ℂ, ball w δ ⊆ η '' Icc a b := by
  intro a b hab hsub hdiam
  have himage : η '' Icc a b = L '' Icc (v a) (v b) := by
    have heq : η = L ∘ v := funext hη
    rw [heq, Set.image_comp, v.image_Icc]
  rw [himage] at hsub hdiam ⊢
  exact hseg δ ⟨hδ, le_rfl⟩ (v a) (v b) (v.strictMono hab) hsub hdiam

/-- A cell of mass at most `m` meeting `B_ρ` has diameter at most `2D` if
large enough subsegments in `B_R` contain a `δ`-ball and those balls have
mass strictly exceeding `m`. No probabilistic uniformity is assumed. -/
theorem diam_segment_le_of_local_ball_mass {η : ℝ → ℂ} (hη : Continuous η)
    {μ : Measure ℂ} {a b ρ R D δ : ℝ} {m : ℝ≥0∞}
    (hD : 0 < D) (hδ : 0 < δ) (hρR : ρ + D ≤ R)
    (hball : ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball (0 : ℂ) R →
      D ≤ diam (η '' Icc a b) → ∃ w : ℂ, ball w δ ⊆ η '' Icc a b)
    (hmass : ∀ z ∈ ball (0 : ℂ) R, m < μ (ball z δ))
    (hcellmass : μ (η '' Icc a b) ≤ m)
    (hmeet : (η '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty) :
    diam (η '' Icc a b) ≤ 2 * D := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hsρ⟩ := hmeet
  have key : ∀ a' b' : ℝ, a ≤ a' → a' < b' → b' ≤ b →
      η '' Icc a' b' ⊆ closedBall (η s) D →
      D ≤ diam (η '' Icc a' b') → False := by
    intro a' b' ha' hab' hb' hsub hdiam
    have hsubR : η '' Icc a' b' ⊆ ball (0 : ℂ) R := by
      intro w hw
      have h1 := mem_closedBall.mp (hsub hw)
      have h2 := mem_ball.mp hsρ
      apply mem_ball.mpr
      have htriangle := dist_triangle w (η s) (0 : ℂ)
      linarith
    obtain ⟨w, hw⟩ := hball a' b' hab' hsubR hdiam
    have hwR : w ∈ ball (0 : ℂ) R := hsubR (hw (mem_ball_self hδ))
    have hle : μ (ball w δ) ≤ m :=
      (measure_mono (hw.trans (Set.image_mono (Icc_subset_Icc ha' hb')))).trans hcellmass
    exact (not_lt_of_ge hle) (hmass w hwR)
  have hclose : ∀ u ∈ Icc a b, dist (η u) (η s) < D := by
    intro u hu
    by_contra hcon
    have hDu : D ≤ dist (η u) (η s) := not_lt.mp hcon
    rcases le_total s u with hsu | hus
    · obtain ⟨t, hst, htu, hsub, hdiam⟩ :=
        MatedCRTHarmonic.GMSLemma27.exists_subsegment_exit_right hη hD hsu hDu
      exact key s t hs.1 hst (htu.trans hu.2) hsub hdiam
    · obtain ⟨t, hut, hts, hsub, hdiam⟩ :=
        MatedCRTHarmonic.GMSLemma27.exists_subsegment_exit_left hη hD hus hDu
      exact key t s (hu.1.trans hut) hts hs.2 hsub hdiam
  refine diam_le_of_forall_dist_le (by linarith) ?_
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have h1 := hclose u hu
  have h2 := hclose v hv
  calc dist (η u) (η v) ≤ dist (η u) (η s) + dist (η s) (η v) := dist_triangle _ _ _
    _ ≤ 2 * D := by rw [dist_comm (η s)]; linarith

/-- The preceding bound applied simultaneously to all mated-CRT cells.
The mass hypothesis follows from area parametrization when `ε > 0`. -/
theorem cell_diam_le_of_local_ball_mass {η : ℝ → ℂ} (hη : Continuous η)
    {μ : Measure ℂ} {ε ρ R D δ : ℝ}
    (hD : 0 < D) (hδ : 0 < δ) (hρR : ρ + D ≤ R)
    (hball : ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball (0 : ℂ) R →
      D ≤ diam (η '' Icc a b) → ∃ w : ℂ, ball w δ ⊆ η '' Icc a b)
    (hmass : ∀ z ∈ ball (0 : ℂ) R, ENNReal.ofReal ε < μ (ball z δ))
    (hcellmass : ∀ i : ℤ, μ (cell ε η i) ≤ ENNReal.ofReal ε) :
    ∀ i : ℤ, (cell ε η i ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε η i) ≤ 2 * D := by
  intro i hi
  exact diam_segment_le_of_local_ball_mass hη hD hδ hρR hball hmass (hcellmass i) hi

/-- Area parametrization gives every positive-mesh cell exactly its mesh mass. -/
theorem cell_mass_of_area_parametrized {η : ℝ → ℂ} {μ : Measure ℂ}
    (harea : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (i : ℤ) :
    μ (cell ε η i) = ENNReal.ofReal ε := by
  have hlt : ε * ((i : ℝ) - 1) < ε * (i : ℝ) := by nlinarith
  have hm := harea.2.2.2 _ _ hlt
  have heq : ε * (i : ℝ) - ε * ((i : ℝ) - 1) = ε := by ring
  simpa only [cell, heq] using hm

/-- The audited cell-size contradiction, with the segment event stated for
its reference curve and the lower-mass event on the full ball `B_(1-δ)`. -/
theorem cell_diam_le_of_segment_event {η : ℝ → ℂ} {μ : Measure ℂ}
    (harea : IsAreaParametrized μ η) (L : C(ℝ, ℂ)) (v : ℝ ≃o ℝ)
    (hη : ∀ t, η t = L (v t)) {ε ρ R δ r β : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hρR : ρ + δ ^ (1 - r) ≤ R) (hR : R ≤ 1 - δ)
    (hεmass : ε < δ ^ β)
    (hseg : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls L R r δ)
    (hmass : ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ β) ≤ μ (ball z δ)) :
    ∀ i : ℤ, (cell ε η i ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε η i) ≤ 2 * δ ^ (1 - r) := by
  apply cell_diam_le_of_local_ball_mass harea.1 (Real.rpow_pos_of_pos hδ _) hδ hρR
  · exact segment_balls_of_reparametrization L η v hη hδ hseg
  · intro z hz
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hδ β)).2 hεmass)
      (hmass z ((ball_subset_ball hR) hz))
  · intro i
    exact (cell_mass_of_area_parametrized harea hε i).le

/-- Validity supplies one reference curve whose increasing reparametrization
and area parametrization hold simultaneously almost surely. -/
theorem MatedCRTEnv.IsValid.exists_ae_area_reparametrization
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ L : Ω → C(ℝ, ℂ),
      (∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧
        ∃ v : ℝ ≃o ℝ, ∀ t, S.η ω t = L ω (v t)) ∧
      ∀ R : ℝ, 0 < R → ∀ r ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, ∃ C : ℝ,
        ∀ δ ∈ Ioo (0 : ℝ) 1,
          S.P {ω | ¬ MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (L ω) R r δ} ≤
            ENNReal.ofReal (C * δ ^ N) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, L, η', η₀, hcoup, hcompat⟩ := hS.matingOfTrees
  refine ⟨L, ?_, hcoup.segmentsContainBalls⟩
  filter_upwards [hS.isAreaParametrized, hcoup.areaParam, hcompat] with ω harea hparam hsame
  obtain ⟨v, _, hv⟩ := hparam.1
  refine ⟨harea, v, ?_⟩
  intro t
  rw [← hsame.1]
  exact hv t

/-- Outer-measure union bound reducing cell-size failure to the area/clock,
segment-ball, and cone ball-mass events. No measurability of these events is
needed for this inequality. -/
theorem cell_diam_failure_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (η : Ω → ℝ → ℂ) (μ : Ω → Measure ℂ) (L : Ω → C(ℝ, ℂ))
    {ε ρ R δ r β : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hρR : ρ + δ ^ (1 - r) ≤ R) (hR : R ≤ 1 - δ)
    (hεmass : ε < δ ^ β) :
    P {ω | ¬ ∀ i : ℤ, (cell ε (η ω) i ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (cell ε (η ω) i) ≤ 2 * δ ^ (1 - r)} ≤
      P {ω | ¬ (IsAreaParametrized (μ ω) (η ω) ∧
          ∃ v : ℝ ≃o ℝ, ∀ t, η ω t = L ω (v t))} +
      P {ω | ¬ MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (L ω) R r δ} +
      P {ω | ¬ ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ β) ≤ μ ω (ball z δ)} := by
  classical
  let A := {ω | ¬ (IsAreaParametrized (μ ω) (η ω) ∧
    ∃ v : ℝ ≃o ℝ, ∀ t, η ω t = L ω (v t))}
  let B := {ω | ¬ MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (L ω) R r δ}
  let C := {ω | ¬ ∀ z ∈ ball (0 : ℂ) (1 - δ),
    ENNReal.ofReal (δ ^ β) ≤ μ ω (ball z δ)}
  have hsub : {ω | ¬ ∀ i : ℤ, (cell ε (η ω) i ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε (η ω) i) ≤ 2 * δ ^ (1 - r)} ⊆ (A ∪ B) ∪ C := by
    intro ω hbad
    by_cases ha : IsAreaParametrized (μ ω) (η ω) ∧
        ∃ v : ℝ ≃o ℝ, ∀ t, η ω t = L ω (v t)
    · by_cases hb : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (L ω) R r δ
      · by_cases hc : ∀ z ∈ ball (0 : ℂ) (1 - δ),
            ENNReal.ofReal (δ ^ β) ≤ μ ω (ball z δ)
        · obtain ⟨v, hv⟩ := ha.2
          exact (hbad (cell_diam_le_of_segment_event ha.1 (L ω) v hv hε hδ hρR hR hεmass hb hc)).elim
        · exact Or.inr hc
      · exact Or.inl (Or.inr hb)
    · exact Or.inl (Or.inl ha)
  calc
    P _ ≤ P ((A ∪ B) ∪ C) := measure_mono hsub
    _ ≤ P (A ∪ B) + P C := measure_union_le _ _
    _ ≤ P A + P B + P C := add_le_add (measure_union_le A B) le_rfl

end MatedCRT.Sec3
