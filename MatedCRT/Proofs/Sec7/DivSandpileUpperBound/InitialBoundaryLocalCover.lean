import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleCoverage
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LocalSampleCover
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalMeasurableCover

/-! Initial boundary estimates using measurable local-cluster covers.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology TopologicalSpace Set Metric _root_.HarmonicBalls

/-- The initial boundary odometer estimate needs no measurability assumption on
the exit event: measurable bounded-cluster frontier samples provide the cover. -/
theorem initial_boundary_odometer_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q : ℝ), 0 < t → 0 < δ → 0 < q →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ε * (⨆ a : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hfixed⟩ := initial_boundary_odometer_of_fixed_localization
    𝒮 h41 h33 hscale γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense ℂ
  refine ⟨C, hC, ?_⟩
  intro t δ q ht hδ hq
  let G : ℕ → Set Ω := fun n => {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω)} ∩
    ⋃ i : ℕ, ⋃ _ : i ≤ n, localSampleLocalization S D ρ t q i
  have hmono : Monotone G := by
    intro n m hnm ω hω
    simp only [G, mem_inter_iff, mem_ofPred_eq, mem_iUnion] at hω ⊢
    obtain ⟨hfam, i, hi, hω⟩ := hω
    exact ⟨hfam, i, hi.trans hnm, hω⟩
  have hmeas : ∀ n, NullMeasurableSet (G n) S.P := by
    intro n
    have hfam : NullMeasurableSet {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω)} S.P := by
      apply nullMeasurableSet_univ.congr
      filter_upwards [hΛ] with ω hω
      simp [hω]
    apply hfam.inter
    apply NullMeasurableSet.iUnion
    intro i
    apply NullMeasurableSet.iUnion
    intro _
    exact nullMeasurableSet_localSampleLocalization hγ hγ' hS h27 hρ hρ' ht D hDcount i
  have heq : ∀ ω, IsConeHarmonicBallFamily (S.μ ω) (Λ ω) →
      t < clusterExitTime (Λ ω) ρ →
      Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) := by
    intro ω hfam hT
    exact (hfam.2.2 t (ρ / 3) ht (by linarith)
      (coneFamily_subset_before_exit hfam ht hT) ρ (by linarith)).1
  have hcover : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n, ω ∈ G n := by
    filter_upwards [hΛ] with ω hfam hT
    obtain ⟨n, hn⟩ := coneFamily_exists_initialSampleLocalization S Λ D hρ ht hq hfam hT
    have hn' : ω ∈ localSampleLocalization S D ρ t q n := by
      simpa [initialSampleLocalization, localSampleLocalization, heq ω hfam hT] using hn.2
    exact ⟨n, hfam, mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨le_rfl, hn'⟩⟩⟩
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply tendsToOneOn_of_ae_measurable_cover S.P _ G _ hmono hmeas hcover
  intro n
  obtain ⟨hr, hO1, hO2, hdist⟩ := initialAnnulus_properties hρ n
  have hn := hfixed t δ q (initialAnnulusRadius ρ n / 2) ht hδ hq.le
    (by positivity) (initialAnnulus ρ n) hO1 hO2 hdist
  unfold TendsToOneOn at hn ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  intro ω hω
  obtain ⟨hT, hG⟩ := hω.1
  simp only [G, mem_inter_iff, mem_ofPred_eq, mem_iUnion] at hG
  obtain ⟨hfam, i, hi, hs⟩ := hG
  have hs' : ω ∈ initialSampleLocalization S Λ D ρ t q i := by
    refine ⟨hT, ?_⟩
    simpa [localSampleLocalization, heq ω hfam hT] using hs
  have hloc := initialSampleLocalization_subset_frontierLocalization S Λ D hDdense hρ ht i hfam hs'
  have hloc' := initialFrontierLocalization_monotone S Λ hρ.le t q hi hloc
  have hd : 2 * (initialAnnulusRadius ρ n / 2) = initialAnnulusRadius ρ n := by ring
  exact ⟨by simpa only [hd, initialFrontierLocalization, mem_ofPred_eq] using hloc', hω.2⟩

/-- The mesh-normalized initial boundary odometer converges to zero before exit. -/
theorem initial_boundary_odometer_tendsToZero_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) :
    ∀ a : ℝ, 0 < a → TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | ε * (⨆ b : vBoundary (S.mult ε ω)
        (cellVertices ε (S.η ω) (Λ ω t)),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b) ≤ a} := by
  obtain ⟨C, hC, hbound⟩ := initial_boundary_odometer_of_local_cluster_cover
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ
  intro a ha
  let b := a / (4 * C)
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall : C * (b + 2 * b) ≤ a := by
    dsimp [b]
    have hC0 : C ≠ 0 := by linarith
    field_simp
    linarith
  have h := hbound t b b ht hb hb
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun ε => measure_mono fun ω hω =>
    ⟨hω.1, fun hgood => hω.2 (hgood.trans hsmall)⟩


end MatedCRT.Sec7
