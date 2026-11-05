import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.InfDistTrace
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable

/-! # Measurability of localized obstacle-gap thresholds -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls

/-- Before exit, a fixed threshold for the obstacle gap on an inner
neighbourhood away from the pole is null measurable from point tests of the
cone-ball trace and continuum gap. -/
theorem nullMeasurableSet_innerNbhd_gap_on_event
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ ρ t δ r b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hρ : 0 < ρ) (ht : 0 < t) (hδ : 0 < δ) (hr : 0 < r)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (E : Set Ω) (hE : NullMeasurableSet E S.P)
    (hEsub : E ⊆ {ω | t < clusterExitTime (Λ ω) ρ})
    (hmem : ∀ j, NullMeasurableSet {ω | ω ∈ E ∧ densePoint j ∈ Λ ω t} S.P)
    (hgap : ∀ m : ℕ, ∀ x ∈ closedBall (0 : ℂ) (ρ / 2) \ ball 0 r,
      NullMeasurableSet {ω | ω ∈ E ∧ b - 1 / ((m : ℝ) + 1) ≤
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∀ x ∈ innerNbhd δ (Λ ω t) \ ball 0 r,
      b ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P := by
  let K : Set ℂ := closedBall (0 : ℂ) (ρ / 2) \ ball 0 r
  let G : Ω → ℂ → ℝ := fun ω x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
    (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) (ρ / 2)).diff isOpen_ball
  have hreg : ∀ᵐ ω ∂S.P, ω ∈ E → interior (closure (Λ ω t)) = Λ ω t := by
    filter_upwards [hΛ] with ω hω _
    exact hω.2.1.isRegularOpen t ht
  have hsub : ∀ᵐ ω ∂S.P, ω ∈ E → Λ ω t ⊆ ball 0 (ρ / 3) := by
    filter_upwards [hΛ, hS.isLQGMeasure] with ω hω hμ hωE
    let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
    obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hω ht).mp (hEsub hωE)
    exact (hω.2.1.monotoneOn ht (ht.trans htq) htq.le).trans hq
  have hne : ∀ᵐ ω ∂S.P, ω ∈ E → (Λ ω t)ᶜ.Nonempty := by
    filter_upwards [hsub] with ω hω hωE
    refine ⟨(ρ : ℂ), ?_⟩
    intro hx
    have hz := hω hωE hx
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hz
    linarith
  have hc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (G ω) K := by
    filter_upwards [hΛ] with ω hω hωE
    have hsubset : K ⊆ closedBall (0 : ℂ) ρ := fun _ hx =>
      closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ) hx.1
    have hpole : K ⊆ ({0} : Set ℂ)ᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hx0
      subst x
      exact hx.2 (mem_ball_self hr)
    exact (continuousOn_const.mul ((coneFamily_leastSupersolution_continuous hω hρ ht
      (hEsub hωE)).mono hsubset)).sub
      (continuousOn_const.mul ((continuousOn_greenFunction_ball (mem_ball_self hρ)).mono hpole))
  have hm := nullMeasurableSet_innerNbhd_compact_inequality_on S.P E hE
    (fun ω => Λ ω t) hreg hne hmem K hK δ hδ G b hgap hc
  apply hm.congr
  filter_upwards [hΛ, hS.isLQGMeasure] with ω hω hμ
  apply propext
  constructor
  · rintro ⟨hωE, h⟩
    let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
    have htarget := (coneFamily_innerNbhd_compact_subset hω hρ ht (hEsub hωE) hδ).2
    refine ⟨hωE, ?_⟩
    intro x hx
    exact h x ⟨htarget hx.1, hx.2⟩ hx.1
  · rintro ⟨hωE, h⟩
    exact ⟨hωE, fun x hx hinner => h x ⟨hinner, hx.2⟩⟩

/-- Lemma 2.7 supplies the localized trace and continuum point tests for
obstacle-gap thresholds inside the unit disc. -/
theorem nullMeasurableSet_innerNbhd_gap_on_event_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ ρ t δ r b : ℝ} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t) (hδ : 0 < δ) (hr : 0 < r)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (E : Set Ω) (hE : NullMeasurableSet E S.P)
    (hEsub : E ⊆ {ω | t < clusterExitTime (Λ ω) ρ}) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∀ x ∈ innerNbhd δ (Λ ω t) \ ball 0 r,
      b ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P := by
  apply nullMeasurableSet_innerNbhd_gap_on_event S hS hρ ht hδ hr Λ hΛ E hE hEsub
  · intro j
    have hm := hE.inter (hS.nullMeasurableSet_mem_regularizedLocalCluster hγ hγ2 h27
      hρ hρ1 ht (densePoint j))
    apply hm.congr
    filter_upwards [hΛ, hS.isLQGMeasure] with ω hω hμ
    apply propext
    constructor
    · rintro ⟨hωE, hx⟩
      let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
      obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hω ht).mp (hEsub hωE)
      have hsub : Λ ω t ⊆ ball 0 (ρ / 3) :=
        (hω.2.1.monotoneOn ht (ht.trans htq) htq.le).trans hq
      have heq := (hω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
      exact ⟨hωE, heq.symm ▸ hx⟩
    · rintro ⟨hωE, hx⟩
      let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
      obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hω ht).mp (hEsub hωE)
      have hsub : Λ ω t ⊆ ball 0 (ρ / 3) :=
        (hω.2.1.monotoneOn ht (ht.trans htq) htq.le).trans hq
      have heq := (hω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
      refine ⟨hωE, ?_⟩
      change densePoint j ∈ interior (closure (cluster (S.μ ω) ρ 0 t))
      rw [← heq]
      exact hx
  · intro m x hx
    have hxρ : x ∈ closedBall (0 : ℂ) ρ :=
      closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ) hx.1
    have hv := hS.aemeasurable_leastSupersolution_inside_unit hγ hγ2 h27
      hρ hρ1 ht (mem_ball_self hρ) hxρ
    have hg : AEMeasurable (fun ω => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) S.P :=
      (aemeasurable_const.mul hv).sub aemeasurable_const
    exact hE.inter (nullMeasurableSet_le aemeasurable_const hg)

/-- A uniform continuum lower bound is null measurable on a measurable
exit subevent, using the pointwise measurability from Lemma 2.7. -/
theorem nullMeasurableSet_leastSupersolution_lower_on_event
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (E : Set Ω) (hE : NullMeasurableSet E S.P)
    (hEsub : E ⊆ {ω | t < clusterExitTime (Λ ω) ρ}) (L : ℝ) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∀ x ∈ ball (0 : ℂ) ρ,
      L ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x} S.P := by
  let B : Set ℂ := ball 0 ρ
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense B
  let : Countable D := hDc.to_subtype
  have hpoint : ∀ x : D, NullMeasurableSet {ω | L ≤ S.c₀ / 6 *
      leastSupersolution (S.μ ω) ρ 0 t x.1.1} S.P := by
    intro x
    have hv := hS.aemeasurable_leastSupersolution_inside_unit hγ hγ2 h27 hρ hρ1 ht
      (mem_ball_self hρ) (ball_subset_closedBall x.1.2)
    exact nullMeasurableSet_le aemeasurable_const (aemeasurable_const.mul hv)
  have hm := hE.inter (NullMeasurableSet.iInter hpoint)
  apply hm.congr
  filter_upwards [hΛ] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
  constructor
  · rintro ⟨hωE, h⟩
    have hc : Continuous (fun x : B => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x.1) :=
      continuousOn_iff_continuous_domRestrict.mp (continuousOn_const.mul
        ((coneFamily_leastSupersolution_continuous hω hρ ht (hEsub hωE)).mono ball_subset_closedBall))
    have hclosed : IsClosed {x : B | L ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x.1} :=
      isClosed_le continuous_const hc
    have hsub : D ⊆ {x : B | L ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x.1} :=
      fun x hx => h ⟨x, hx⟩
    refine ⟨hωE, fun x hx => ?_⟩
    exact closure_minimal hsub hclosed (hD ⟨x, hx⟩)
  · rintro ⟨hωE, h⟩
    exact ⟨hωE, fun x => h x.1.1 x.1.2⟩

/-- The pole and gap localization thresholds are null measurable from
Lemma 2.7 and null measurability of the cone-ball exit event. -/
theorem nullMeasurableSet_innerNbhd_gap_threshold_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ ρ t δ r L b : ℝ} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t) (hδ : 0 < δ) (hr : 0 < r)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      innerNbhd δ (Λ ω t) ⊆ closedBall 0 (ρ / 2) ∧
      (∀ x ∈ ball (0 : ℂ) ρ, L ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
      ∀ x ∈ innerNbhd δ (Λ ω t) \ ball 0 r,
        b ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P := by
  let E : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ ∧
    ∀ x ∈ ball (0 : ℂ) ρ, L ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x}
  have hE : NullMeasurableSet E S.P :=
    nullMeasurableSet_leastSupersolution_lower_on_event S hS h27 hγ hγ2 hρ hρ1 ht
      Λ hΛ _ hexit (subset_refl _) L
  have hEsub : E ⊆ {ω | t < clusterExitTime (Λ ω) ρ} := fun _ hω => hω.1
  have hm := nullMeasurableSet_innerNbhd_gap_on_event_of_volumeGrowth S (b := b) hS h27 hγ hγ2
    hρ hρ1 ht hδ hr Λ hΛ E hE hEsub
  apply hm.congr
  filter_upwards [hΛ, hS.isLQGMeasure] with ω hω hμ
  apply propext
  constructor
  · rintro ⟨⟨hT, hlower⟩, hgap⟩
    let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
    exact ⟨hT, (coneFamily_innerNbhd_compact_subset hω hρ ht hT hδ).2, hlower, hgap⟩
  · rintro ⟨hT, _, hlower, hgap⟩
    exact ⟨⟨hT, hlower⟩, hgap⟩

/-- Inner-neighbourhood coverage under the strict obstacle-gap condition,
with threshold measurability derived from Lemma 2.7 and exit measurability. -/
theorem innerNbhd_coverage_of_strict_gap_of_volumeGrowth (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (hgap : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      ∀ x ∈ innerNbhd δ (Λ ω t) \ {0},
        0 < S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      (fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
  obtain ⟨r, hr, hcov⟩ := innerNbhd_coverage_of_strict_gap 𝒮 h41 h33 h28
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ ht
  apply hcov ?_ hgap
  intro n m
  exact nullMeasurableSet_innerNbhd_gap_threshold_of_volumeGrowth S hS h27 hγ hγ'
    hρ hρ' ht hδ (hr n) Λ hΛ hexit

end MatedCRT
