import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DenseConvergenceEvent

/-! # Event measurability from pathwise convergence -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- Pathwise uniform convergence supplies a jointly measurable version of the
continuum field on every measurable subset of the cluster exit event. -/
theorem exists_continuum_version_on_exit_of_pathwise
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (E : Set Ω) (hEsub : E ⊆ {ω | t < clusterExitTime (Λ ω) ρ}) :
    ∃ f : Ω × ℂ → ℝ, Measurable f ∧ ∀ᵐ ω ∂S.P, ω ∈ E →
      ∀ x ∈ ball (0 : ℂ) ρ, f (ω, x) =
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x := by
  let εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < εs n := fun n => by dsimp [εs]; positivity
  have hε0 : Tendsto εs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, hpath⟩ := convergenceDivisible_pathwise_of_steps 𝒮 h48 h46 hu
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ εs hε hε0
  have hlf := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' hcell
  have hversion : ∀ n, ∃ F : Ω × ℂ → ℝ, Measurable F ∧ ∀ᵐ ω ∂S.P, ∀ x,
      F (ω, x) = rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x := by
    intro n
    apply hS.exists_measurable_rescaledMatedLeastSupersolution hγ hγ' (hε (φ n)) ρ t ht
    filter_upwards [hlf] with ω hω
    exact hω _ (hε (φ n))
  choose F hF hFae using hversion
  let f : Ω × ℂ → ℝ := fun p => limUnder atTop (fun n => F n p)
  have hf : Measurable f := (StronglyMeasurable.limUnder
    (fun n => (hF n).stronglyMeasurable)).measurable
  refine ⟨f, hf, ?_⟩
  filter_upwards [hpath, ae_all_iff.mpr hFae] with ω hω hFω hωE x hx
  have hT : t < clusterExitTime (Λ ω) ρ := hEsub hωE
  have hconv := (hω t ht hT).tendsto_at (ball_subset_closedBall hx)
  have hconv' : Tendsto (fun n => F n (ω, x)) atTop
      (𝓝 (S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x)) := by
    convert hconv using 1
    funext n
    exact hFω n x
  exact hconv'.limUnder_eq

/-- Given a measurable cluster exit event, pathwise convergence makes the
convergence error event measurable without a separate continuum construction. -/
theorem nullMeasurableSet_convergenceError_of_pathwise
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ t δ ε : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t) (hε : 0 < ε)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} S.P := by
  obtain ⟨E, hEsub, hE, hEae⟩ := hexit.exists_measurable_subset_ae_eq
  obtain ⟨f, hf, hfae⟩ := exists_continuum_version_on_exit_of_pathwise hS hγ hγ' hρ hρ' ht
    Λ hΛ h48 h46 hu hcell E hEsub
  have hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) (ball 0 ρ) := by
    filter_upwards [hΛ, hfae] with ω hω hfω hωE
    have hT : t < clusterExitTime (Λ ω) ρ := hEsub hωE
    exact (continuousOn_const.mul
      ((coneFamily_leastSupersolution_continuous hω hρ ht hT).mono ball_subset_closedBall)).congr
        (fun x hx => hfω hωE x hx)
  have hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite := by
    filter_upwards [ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' hcell] with ω hω
    exact hω ε hε
  have hm := hS.nullMeasurableSet_matedLeast_deviation_on_event hγ hγ' hε ρ t ht hlf
    isOpen_ball isBounded_ball f hf E hE hfc δ
  apply hm.congr
  filter_upwards [hEae, hfae] with ω he hfω
  apply propext
  have he' : ω ∈ E ↔ t < clusterExitTime (Λ ω) ρ := iff_of_eq he
  constructor
  · rintro ⟨hEω, x, hx, hd⟩
    exact ⟨he'.mp hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩
  · rintro ⟨hT, x, hx, hd⟩
    have hEω := he'.mpr hT
    exact ⟨hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩

/-- The convergence theorem follows from its pathwise inputs, adjacent-cell
intersection, and measurability of the cluster exit event. -/
theorem convergenceDivisible_of_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hexit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 := by
  apply convergenceDivisible_of_steps 𝒮 h48 h46 hu
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t δ ε ht _ hε
  exact nullMeasurableSet_convergenceError_of_pathwise hS hγ hγ' hρ hρ' ht hε Λ hΛ
    h48 h46 hu hcell (hexit γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht)

/-- It is enough to verify continuum measurability at integer radii, positive
rational times and a fixed countable dense set of spatial points. -/
theorem convergenceDivisible_of_countable_continuum_evaluations
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (C : Set ℂ) (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (n : ℕ) (z : ℂ), z ∈ C → AEMeasurable
        (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q z) S.P) :
    ConvergenceDivisibleStmt 𝒮 := by
  apply convergenceDivisible_of_measurable_exit 𝒮 h48 h46 hu hcell
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t ht
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ z : ℂ,
      NullMeasurableSet {ω | z ∈ Λ ω q} S.P := by
    intro q hq z
    exact nullMeasurableSet_mem_coneFamily_of_dense_leastSupersolutions S.P S.μ Λ q hq hΛ
      hC hdense hzero (hpoint γ hγ hγ' Ω S hS q hq) z
  exact nullMeasurableSet_lt_clusterExitTime_of_membership S.P S.μ Λ hΛ hloc hmem ρ t ht

/-- The event-measurability step follows from the pathwise inputs and null
measurability of cluster exit events. -/
theorem convergenceDivisibleEventMeasurable_of_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hexit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t δ ε ht _ hε
  exact nullMeasurableSet_convergenceError_of_pathwise hS hγ hγ' hρ hρ' ht hε Λ hΛ
    h48 h46 hu hcell (hexit γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht)

/-- Countably many continuum evaluations suffice for the event-measurability
step once pathwise convergence has been established. -/
theorem convergenceDivisibleEventMeasurable_of_countable_continuum_evaluations
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (C : Set ℂ) (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (n : ℕ) (z : ℂ), z ∈ C → AEMeasurable
        (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q z) S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_measurable_exit 𝒮 h48 h46 hu hcell
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t ht
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ z : ℂ,
      NullMeasurableSet {ω | z ∈ Λ ω q} S.P := by
    intro q hq z
    exact nullMeasurableSet_mem_coneFamily_of_dense_leastSupersolutions S.P S.μ Λ q hq hΛ
      hC hdense hzero (hpoint γ hγ hγ' Ω S hS q hq) z
  exact nullMeasurableSet_lt_clusterExitTime_of_membership S.P S.μ Λ hΛ hloc hmem ρ t ht

end MatedCRT
