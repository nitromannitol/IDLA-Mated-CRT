import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.PoleCellSize
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparisonProved
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitCDF
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitTime

/-! # Coverage near the pole in probability -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Before cluster exit, the scaled continuum least supersolution has a
finite uniform lower bound on the comparison ball. -/
theorem exists_lower_bound_scaled_leastSupersolution
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t : ℝ} (c : ℝ)
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) :
    ∃ L : ℝ, L < 0 ∧ ∀ x ∈ ball (0 : ℂ) ρ,
      L + 2 ≤ c * leastSupersolution μ ρ 0 t x := by
  have hc : ContinuousOn (fun x => c * leastSupersolution μ ρ 0 t x) (closedBall 0 ρ) :=
    continuousOn_const.mul (coneFamily_leastSupersolution_continuous hΛ hρ ht hT)
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_isMinOn
    ⟨0, mem_closedBall_self hρ.le⟩ hc
  refine ⟨min (c * leastSupersolution μ ρ 0 t z - 2) (-1), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro x hx
    have h := hmin (ball_subset_closedBall hx)
    change c * leastSupersolution μ ρ 0 t z ≤ c * leastSupersolution μ ρ 0 t x at h
    have hl := min_le_left (c * leastSupersolution μ ρ 0 t z - 2) (-1)
    linarith

/-- For any deterministic lower bound on the continuum least supersolution,
a fixed neighbourhood of the pole is covered in probability on that event. -/
theorem pole_coverage_on_lower_bound (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t L : ℝ) (ht : 0 < t) (hL : L < 0) :
    ∃ r : ℝ, 0 < r ∧ TendsToOneOn S.P
      {ω | t < clusterExitTime (Λ ω) ρ ∧ ∀ x ∈ ball (0 : ℂ) ρ,
        L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x}
      (fun ε => {ω | ball (0 : ℂ) r ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
  have hc : 0 < S.c₀ / 6 := by
    have := matedCRTScalingConstantPositive 𝒮 γ hγ hγ' Ω S hS
    positivity
  obtain ⟨r, hr, hrρ, hgreen⟩ := exists_scaled_green_barrier_near_zero
    (δ := 1) (L := L) hρ ht hc
  let K : Set ℂ := closedBall 0 (2 * r) \ ball 0 (r / 2)
  have hKsub : K ⊆ closedBall 0 ρ \ {0} := by
    intro x hx
    have hhi : dist x 0 ≤ 2 * r := hx.1
    have hlo : r / 2 ≤ dist x 0 := le_of_not_gt hx.2
    constructor
    · change dist x 0 ≤ ρ
      linarith
    · simp only [mem_singleton_iff]
      intro hx0
      subst x
      simp only [dist_self] at hlo
      linarith
  have hKne : K.Nonempty := by
    refine ⟨(r : ℂ), ?_, ?_⟩
    · change dist (r : ℂ) 0 ≤ 2 * r
      simpa using (show |r| ≤ 2 * r by rw [abs_of_pos hr]; linarith)
    · change ¬ dist (r : ℂ) 0 < r / 2
      simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      linarith
  have hKdist : 0 < infDist (0 : ℂ) K := by
    apply lt_of_lt_of_le (show 0 < r / 2 by positivity)
    apply (le_infDist hKne).2
    intro x hx
    have hlo : r / 2 ≤ dist x 0 := le_of_not_gt hx.2
    simpa only [dist_comm] using hlo
  have hw := h41 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht 1 (by norm_num)
  have hφ := obstacle_convergence_off_origin 𝒮 h33 γ hγ hγ' ρ hρ hρ' Ω S hS
    t 1 ht (by norm_num) K hKsub hKdist
  have hdiam := small_cells_in_probability 𝒮 h28 hγ hγ'
    (show 0 < r + r / 4 by positivity) (show r + r / 4 < 1 by linarith)
    (show 0 < r / 4 by positivity) Ω S hS
  have hgood := hφ.inter hdiam
  unfold ProbTendsToOne at hgood
  refine ⟨r, hr, ?_⟩
  unfold TendsToOneOn
  have hsum := hw.add hgood
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply le_trans ?_ (measure_union_le _ _)
  apply measure_mono_ae
  filter_upwards [hS.ae_tendsto_cocompact, hS.isAreaParametrized,
    hS.ae_vertexOf_zero_eq_zero, (adjacentCellsMeetAeStep 𝒮) γ hγ hγ' Ω S hS,
    hS.ae_isLocallyFiniteMult hγ hγ' (adjacentCellsMeetAeStep 𝒮)] with ω hp harea hsource hcell hlf
  rintro ⟨⟨hT, hlower⟩, hbad⟩
  by_cases hwbad : ∃ x ∈ ball (0 : ℂ) ρ,
      1 < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|
  · exact Or.inl ⟨hT, hwbad⟩
  · by_cases hgoodω : ω ∈ {ω | ∀ x ∈ K,
        |rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)| ≤ 1} ∩
        {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 (r + r / 4)),
          ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ r / 4}
    · exfalso
      apply hbad
      apply ball_subset_fillCells_of_continuum_pole_bounds
        (w := fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x)
        harea hp hε ht.le hr (by norm_num)
        hrρ (medianOf_nonneg _) hL (hsource ε hε) (S.mult_symm ε ω) (hlf ε hε)
        (S.mult_succ_ne_zero hε.le ω) (hcell ε hε) hgoodω.2 hgreen (by simpa using hlower)
      · intro x hx
        exact le_of_not_gt (fun h => hwbad ⟨x, hx, h⟩)
      · intro x hlo hhi
        apply hgoodω.1 x
        constructor
        · change dist x 0 ≤ 2 * r
          simpa only [dist_zero_right] using hhi
        · change ¬ dist x 0 < r / 2
          simpa only [dist_zero_right, not_lt] using hlo
    · exact Or.inr hgoodω

/-- A countable family of deterministic pole radii covers every sample before
cluster exit in the sense that its corresponding lower-bound event holds. -/
theorem pole_coverage_on_exhausting_events (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      (∀ n : ℕ, TendsToOneOn S.P
        {ω | t < clusterExitTime (Λ ω) ρ ∧ ∀ x ∈ ball (0 : ℂ) ρ,
          -((n : ℝ) + 3) + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x}
        (fun ε => {ω | ball (0 : ℂ) (r n) ⊆ fillCells ε (S.η ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) ∧
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n : ℕ,
        ∀ x ∈ ball (0 : ℂ) ρ,
          -((n : ℝ) + 3) + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) := by
  have hcov : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ TendsToOneOn S.P
      {ω | t < clusterExitTime (Λ ω) ρ ∧ ∀ x ∈ ball (0 : ℂ) ρ,
        -((n : ℝ) + 3) + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x}
      (fun ε => {ω | ball (0 : ℂ) r ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
    intro n
    exact pole_coverage_on_lower_bound 𝒮 h41 h33 h28 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
      t (-((n : ℝ) + 3)) ht (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  choose r hr hprob using hcov
  refine ⟨r, hr, hprob, ?_⟩
  filter_upwards [hΛ] with ω hΛω hT
  obtain ⟨L, _, hL⟩ := exists_lower_bound_scaled_leastSupersolution (S.c₀ / 6) hΛω hρ ht hT
  obtain ⟨n, hn⟩ := exists_nat_gt (-L)
  refine ⟨n, ?_⟩
  intro x hx
  have := hL x hx
  linarith

end MatedCRT
