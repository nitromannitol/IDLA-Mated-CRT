import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleExtension

/-! Coverage by sampled frontier localizations.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology TopologicalSpace Set Metric _root_.HarmonicBalls

/-- Before exit, some sampled frontier-localization event occurs. -/
theorem coneFamily_exists_initialSampleLocalization
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Λ : Ω → ℝ → Set ℂ) (C : Set ℂ) {ρ t q : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hq : 0 < q) {ω : Ω}
    (hfam : IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hT : t < clusterExitTime (Λ ω) ρ) :
    ∃ n, ω ∈ initialSampleLocalization S Λ C ρ t q n := by
  obtain ⟨d, hd, O, _, _, hdist, hsub, hgap⟩ :=
    coneFamily_exists_frontier_annulus (c := S.c₀ / 6) hfam hρ ht hT hq
  let b := min d (min (infDist (0 : ℂ) O / 2) (ρ / 9))
  have hb : 0 < b := lt_min hd (lt_min (by positivity) (by positivity))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hb hρ)
  have hinv : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hsmall : initialAnnulusRadius ρ n < b := by
    have h := mul_lt_mul_of_pos_left (hinv.trans_lt hn) hρ
    have heq : ρ * (b / ρ) = b := by field_simp
    rw [heq] at h
    convert h using 1; unfold initialAnnulusRadius; ring
  have hr : 0 < initialAnnulusRadius ρ n := (initialAnnulus_properties hρ n).1
  have hrd : initialAnnulusRadius ρ n < d := hsmall.trans_le (min_le_left _ _)
  have hrO : 2 * initialAnnulusRadius ρ n < infDist (0 : ℂ) O := by
    have h := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hrρ : initialAnnulusRadius ρ n < ρ / 9 :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hfront : frontier (Λ ω t) ⊆ closedBall (0 : ℂ) (ρ / 3) :=
    frontier_subset_closure.trans (closure_minimal
      ((coneFamily_subset_before_exit hfam ht hT).trans ball_subset_closedBall) isClosed_closedBall)
  refine ⟨n, hT, ?_⟩
  intro x _ hx
  have hxcl : x ∈ cthickening (2 * d) (frontier (Λ ω t)) :=
    cthickening_mono (by linarith) _ (thickening_subset_cthickening _ _ hx)
  have hxO := hsub hxcl
  have hxinf : infDist (0 : ℂ) O ≤ dist 0 x := infDist_le_dist_of_mem hxO
  have hinner : initialAnnulusRadius ρ n ≤ dist x 0 := by
    rw [dist_comm] at hxinf
    linarith
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  have hyball := hfront hy
  rw [mem_closedBall] at hyball
  have hxy0 : dist x 0 ≤ dist x y + dist y 0 := dist_triangle x y 0
  have houter : x ∈ closedBall 0 (ρ - initialAnnulusRadius ρ n) := by
    rw [mem_closedBall]
    linarith
  refine ⟨houter, hinner, ?_⟩
  have hh := (hgap x hxcl).le
  convert hh using 1; ring

/-- A measurable before-exit event permits a countable sampled exhaustion in
the initial boundary-odometer estimate. -/
theorem initial_boundary_odometer_of_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q : ℝ), 0 < t → 0 < δ → 0 < q →
      NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ε * (⨆ a : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hlocal⟩ := initial_boundary_odometer_of_localization_exhaustion
    𝒮 h41 h33 hscale γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense ℂ
  refine ⟨C, hC, ?_⟩
  intro t δ q ht hδ hq hexit
  let G : ℕ → Set Ω := fun n => {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω)} ∩
    ⋃ i : ℕ, ⋃ _ : i ≤ n, initialSampleLocalization S Λ D ρ t q i
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
    exact nullMeasurableSet_initialSampleLocalization hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit D hDcount i
  have hcover : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n, ω ∈ G n := by
    filter_upwards [hΛ] with ω hfam hT
    obtain ⟨n, hn⟩ := coneFamily_exists_initialSampleLocalization S Λ D hρ ht hq hfam hT
    exact ⟨n, hfam, mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨le_rfl, hn⟩⟩⟩
  apply hlocal t δ q ht hδ hq.le G (fun n => initialAnnulusRadius ρ n / 2) (initialAnnulus ρ)
    hmono hmeas hcover
  · intro n
    obtain ⟨hr, hO1, hO2, hdist⟩ := initialAnnulus_properties hρ n
    exact ⟨by positivity, hO1, hO2, hdist⟩
  · intro n ω hω
    simp only [G, mem_inter_iff, mem_ofPred_eq, mem_iUnion] at hω
    obtain ⟨hfam, i, hi, hω⟩ := hω
    have hs := initialSampleLocalization_subset_frontierLocalization S Λ D hDdense hρ ht i hfam hω
    have hs' := initialFrontierLocalization_monotone S Λ hρ.le t q hi hs
    have heq : 2 * (initialAnnulusRadius ρ n / 2) = initialAnnulusRadius ρ n := by ring
    rw [heq]
    exact hs'

/-- The mesh-normalized initial boundary odometer converges to zero before a
null-measurable exit event. -/
theorem initial_boundary_odometer_tendsToZero_of_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ∀ a : ℝ, 0 < a → TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | ε * (⨆ b : vBoundary (S.mult ε ω)
        (cellVertices ε (S.η ω) (Λ ω t)),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b) ≤ a} := by
  obtain ⟨C, hC, hbound⟩ := initial_boundary_odometer_of_measurable_exit
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ
  intro a ha
  let b := a / (4 * C)
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall : C * (b + 2 * b) ≤ a := by
    dsimp [b]
    have hC0 : C ≠ 0 := by linarith
    field_simp
    linarith
  have h := hbound t b b ht hb hb hexit
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun ε => measure_mono fun ω hω =>
    ⟨hω.1, fun hgood => hω.2 (hgood.trans hsmall)⟩

end MatedCRT.Sec7
