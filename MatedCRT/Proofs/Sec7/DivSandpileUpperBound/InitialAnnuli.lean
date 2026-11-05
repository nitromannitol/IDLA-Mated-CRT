import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialLocalization
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.FrontierAnnulus

/-! Countable frontier localizations for the initial odometer estimate.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- Radius of the `n`th frontier localization. -/
noncomputable def initialAnnulusRadius (ρ : ℝ) (n : ℕ) : ℝ := ρ / ((n : ℝ) + 2)

/-- The `n`th deterministic annulus around the origin. -/
def initialAnnulus (ρ : ℝ) (n : ℕ) : Set ℂ :=
  ball 0 ρ \ ball 0 (initialAnnulusRadius ρ n)

/-- The `n`th before-exit frontier-localization event. -/
def initialFrontierLocalization {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Λ : Ω → ℝ → Set ℂ) (ρ t q : ℝ) (n : ℕ) : Set Ω := {ω |
  t < clusterExitTime (Λ ω) ρ ∧
  cthickening (initialAnnulusRadius ρ n) (frontier (Λ ω t)) ⊆ initialAnnulus ρ n ∧
  ∀ x ∈ cthickening (initialAnnulusRadius ρ n) (frontier (Λ ω t)),
    S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
      (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q}

/-- Localization radii decrease with the index. -/
theorem initialAnnulusRadius_antitone {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Antitone (initialAnnulusRadius ρ) := by
  intro n m hnm
  unfold initialAnnulusRadius
  apply div_le_div_of_nonneg_left hρ (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 2

/-- Frontier-localization events increase with the index. -/
theorem initialFrontierLocalization_monotone {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (t q : ℝ) : Monotone (initialFrontierLocalization S Λ ρ t q) := by
  intro n m hnm ω hω
  have hr := initialAnnulusRadius_antitone hρ hnm
  have hthick := cthickening_mono hr (frontier (Λ ω t))
  refine ⟨hω.1, ?_, fun x hx => hω.2.2 x (hthick hx)⟩
  intro x hx
  have hx' := hω.2.1 (hthick hx)
  refine ⟨hx'.1, ?_⟩
  intro hxm
  exact hx'.2 (ball_subset_ball hr hxm)

/-- The countable localization events cover the before-exit event almost surely. -/
theorem initialFrontierLocalization_ae_cover {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {ρ t q : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hq : 0 < q) :
    ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      ∃ n, ω ∈ initialFrontierLocalization S Λ ρ t q n := by
  filter_upwards [hΛ] with ω hω hT
  obtain ⟨n, hsub, hgap⟩ := coneFamily_exists_countable_frontier_annulus
    (c := S.c₀ / 6) hω hρ ht hT hq
  refine ⟨n, hT, hsub, ?_⟩
  intro x hx
  have h := (hgap x hx).le
  convert h using 1; ring


/-- Every deterministic annulus is contained in the comparison ball and is
separated from the source. -/
theorem initialAnnulus_properties {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 < initialAnnulusRadius ρ n ∧ initialAnnulus ρ n ⊆ ball 0 ρ ∧
    initialAnnulus ρ n ⊆ closedBall (0 : ℂ) ρ \ {0} ∧
    0 < infDist (0 : ℂ) (initialAnnulus ρ n) := by
  have hr : 0 < initialAnnulusRadius ρ n := by unfold initialAnnulusRadius; positivity
  have hrhalf : initialAnnulusRadius ρ n ≤ ρ / 2 := by
    unfold initialAnnulusRadius
    apply (div_le_iff₀ (show 0 < (n : ℝ) + 2 by positivity)).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hne : (initialAnnulus ρ n).Nonempty := by
    refine ⟨((3 * ρ / 4 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < 3 * ρ / 4 by positivity)]
      linarith
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < 3 * ρ / 4 by positivity)]
      linarith
  refine ⟨hr, sdiff_subset, ?_, ?_⟩
  · intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    intro hx0
    apply hx.2
    simpa [Set.mem_singleton_iff.mp hx0] using
      (mem_ball_self hr : (0 : ℂ) ∈ ball 0 (initialAnnulusRadius ρ n))
  · refine lt_of_lt_of_le hr ((le_infDist hne).2 ?_)
    intro x hx
    have hx' := hx.2
    rw [mem_ball] at hx'
    rw [dist_comm]
    exact le_of_not_gt hx'


/-- Null measurability of the countable annulus events supplies the initial
boundary estimate on the entire before-exit event. -/
theorem initial_boundary_odometer_of_measurable_annuli
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q : ℝ), 0 < t → 0 < δ → 0 < q →
      (∀ n, NullMeasurableSet (initialFrontierLocalization S Λ ρ t q n) S.P) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ε * (⨆ a : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hlocal⟩ := initial_boundary_odometer_of_localization_exhaustion
    𝒮 h41 h33 hscale γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro t δ q ht hδ hq hmeas
  apply hlocal t δ q ht hδ hq.le (initialFrontierLocalization S Λ ρ t q)
    (fun n => initialAnnulusRadius ρ n / 2) (initialAnnulus ρ)
    (initialFrontierLocalization_monotone S Λ hρ.le t q) hmeas
    (initialFrontierLocalization_ae_cover S Λ hΛ hρ ht hq)
  · intro n
    obtain ⟨hr, hO1, hO2, hdist⟩ := initialAnnulus_properties hρ n
    exact ⟨by positivity, hO1, hO2, hdist⟩
  · intro n ω hω
    have heq : 2 * (initialAnnulusRadius ρ n / 2) = initialAnnulusRadius ρ n := by ring
    rw [heq]
    exact hω


/-- Measurable countable localizations imply that the initial boundary
odometer, multiplied by the mesh, converges to zero in probability. -/
theorem initial_boundary_odometer_tendsToZero_of_measurable_annuli
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hmeas : ∀ q : ℝ, 0 < q → ∀ n,
      NullMeasurableSet (initialFrontierLocalization S Λ ρ t q n) S.P) :
    ∀ a : ℝ, 0 < a → TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | ε * (⨆ b : vBoundary (S.mult ε ω)
        (cellVertices ε (S.η ω) (Λ ω t)),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b) ≤ a} := by
  obtain ⟨C, hC, hbound⟩ := initial_boundary_odometer_of_measurable_annuli
    𝒮 h41 h33 hscale γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  intro a ha
  let b := a / (4 * C)
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall : C * (b + 2 * b) ≤ a := by
    dsimp [b]
    have hC0 : C ≠ 0 := by linarith
    field_simp
    linarith
  have h := hbound t b b ht hb hb (hmeas b hb)
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun ε => measure_mono fun ω hω =>
    ⟨hω.1, fun hgood => hω.2 (hgood.trans hsmall)⟩

end MatedCRT.Sec7
