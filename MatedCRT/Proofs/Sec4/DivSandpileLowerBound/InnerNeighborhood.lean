import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.PoleAndGap
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClusterExitMeasurable

/-! # Compact inner neighbourhoods of cone harmonic balls -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory _root_.HarmonicBalls

/-- At positive distance, the membership condition in an inner neighbourhood
is implied by its distance condition. -/
theorem innerNbhd_eq_infEDist_superlevel {δ : ℝ} (hδ : 0 < δ) (U : Set ℂ) :
    innerNbhd δ U = {x | ENNReal.ofReal δ ≤ infEDist x Uᶜ} := by
  ext x
  constructor
  · exact fun hx => hx.2
  · intro hx
    change ENNReal.ofReal δ ≤ infEDist x Uᶜ at hx
    refine ⟨?_, hx⟩
    by_contra hxu
    have hz : infEDist x Uᶜ = 0 := infEDist_zero_of_mem hxu
    rw [hz] at hx
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hδ)) hx

/-- A positive inner neighbourhood is closed, regardless of the underlying set. -/
theorem isClosed_innerNbhd {δ : ℝ} (hδ : 0 < δ) (U : Set ℂ) :
    IsClosed (innerNbhd δ U) := by
  rw [innerNbhd_eq_infEDist_superlevel hδ]
  exact isClosed_le continuous_const continuous_infEDist

/-- A positive inner neighbourhood of a bounded set is compact. -/
theorem isCompact_innerNbhd {δ : ℝ} (hδ : 0 < δ) {U : Set ℂ}
    (hU : Bornology.IsBounded U) : IsCompact (innerNbhd δ U) :=
  isCompact_of_isClosed_isBounded (isClosed_innerNbhd hδ U) (hU.subset fun _ hx => hx.1)

/-- Before exit the inner neighbourhood is compact and lies in the inner
comparison disc. -/
theorem coneFamily_innerNbhd_compact_subset {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} {ρ t δ : ℝ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    (hρ : 0 < ρ) (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) (hδ : 0 < δ) :
    IsCompact (innerNbhd δ (Λ t)) ∧ innerNbhd δ (Λ t) ⊆ closedBall 0 (ρ / 2) := by
  obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hΛ ht).mp hT
  have hsub : Λ t ⊆ ball 0 (ρ / 3) :=
    (hΛ.2.1.monotoneOn ht (ht.trans htq) htq.le).trans hq
  constructor
  · exact isCompact_innerNbhd hδ (isBounded_ball.subset hsub)
  · intro x hx
    have hx' : dist x (0 : ℂ) < ρ / 3 := hsub hx.1
    change dist x (0 : ℂ) ≤ ρ / 2
    linarith

/-- Inner-neighbourhood coverage follows from positive obstacle gap away from
the pole and null measurability of the localized threshold events. -/
theorem innerNbhd_coverage_of_strict_gap (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      ((∀ n m : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
        innerNbhd δ (Λ ω t) ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ innerNbhd δ (Λ ω t) \ ball 0 (r n), 1 / ((m : ℝ) + 1) ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) →
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        ∀ x ∈ innerNbhd δ (Λ ω t) \ {0},
          0 < S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
        (fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) := by
  let K : Ω → Set ℂ := fun ω => innerNbhd δ (Λ ω t)
  obtain ⟨r, hr, hcov⟩ := pole_and_compact_strict_gap_coverage_in_probability
    𝒮 h41 h33 h28 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht K
  refine ⟨r, hr, ?_⟩
  intro hmeas hgap
  have h := hcov hmeas
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hΛ, hS.isLQGMeasure, hgap] with ω hΛω hμ hgapω
  rintro ⟨hT, hbad⟩
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨hcompact, hsub⟩ := coneFamily_innerNbhd_compact_subset hΛω hρ ht hT hδ
  have hcont : ContinuousOn (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
      (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) (K ω \ {0}) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.mul ((coneFamily_leastSupersolution_continuous hΛω hρ ht hT).mono
        (fun x hx => closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ) (hsub hx.1)))
    · exact continuousOn_const.mul ((continuousOn_greenFunction_ball (mem_ball_self hρ)).mono
        (fun x hx => hx.2))
  exact ⟨⟨hT, hsub, hcompact, hcont, hgapω hT⟩, hbad⟩

end MatedCRT
