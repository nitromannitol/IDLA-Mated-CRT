import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ContinuumFrontier
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalCutoff
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Small cells in graph closures of sets contained in the inner ball.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric

/-- Uniform smallness in probability of the cells in the graph closure of
any set contained in the inner ball. -/
theorem probTendsToOne_small_cells_initial_closure
    (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2)
    (ρ d : ℝ) (hρ : 0 < ρ) (hd : 0 < d)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ProbTendsToOne S.P fun ε => {ω | ∀ O : Set ℂ, O ⊆ ball 0 (ρ / 3) →
      ∀ a ∈ vClosure (S.mult ε ω) (cellVertices ε (S.η ω) O),
        diam (cell ε (S.η ω) a) ≤ d} := by
  let D := min d (ρ / 3)
  have hD : 0 < D := lt_min hd (by positivity)
  have hgood : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧
      ∀ ε : ℝ, 0 < ε → ∀ a b, S.mult ε ω a b ≠ 0 →
        (cell ε (S.η ω) a ∩ cell ε (S.η ω) b).Nonempty :=
    (hS.isAreaParametrized.and (adjacentCellsMeetAeStep 𝒮 γ hγ hγ' Ω S hS)).mono
      (fun _ h => ⟨h.1.1, h.2⟩)
  apply ((probTendsToOne_of_ae hgood).inter (hS.probTendsToOne_small_cells ρ D hD)).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  intro O hO a ha
  have hsub : vClosure (S.mult ε ω) (cellVertices ε (S.η ω) O) ⊆
      cellVertices ε (S.η ω) (ball 0 ρ) := by
    apply cellVertices_closure_subset_ball hω.1.1 hO (D := D) (by dsimp [D]; linarith [min_le_right d (ρ / 3)])
      (hω.1.2 ε hε)
    intro b hb
    apply hω.2 b
    obtain ⟨x, hxb, hxO⟩ := hb
    refine ⟨x, hxb, ?_⟩
    have hx := hO hxO
    rw [mem_ball] at hx ⊢
    linarith
  exact (hω.2 a (hsub ha)).trans (min_le_left _ _)

/-- On a fixed frontier-localization event, the mesh-normalized initial
boundary odometer is controlled in probability by the continuum obstacle gap. -/
theorem initial_boundary_odometer_of_fixed_localization
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q d : ℝ), 0 < t → 0 < δ → 0 ≤ q → 0 < d →
      ∀ O : Set ℂ, O ⊆ ball 0 ρ → O ⊆ closedBall 0 ρ \ {0} →
      0 < infDist (0 : ℂ) O →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
        cthickening (2 * d) (frontier (Λ ω t)) ⊆ O ∧
        ∀ x ∈ cthickening (2 * d) (frontier (Λ ω t)),
          S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * _root_.HarmonicBalls.greenFunction (ball 0 ρ) 0 x) ≤ q}
        fun ε => {ω | ε * (⨆ a : vBoundary (S.mult ε ω)
          (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hmesh⟩ := mesh_odometer_le_of_small_continuum_gap 𝒮 h41 h33 hscale
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro t δ q d ht hδ hq hd O hO hO' hdist
  let F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ ∧
    cthickening (2 * d) (frontier (Λ ω t)) ⊆ O ∧
    ∀ x ∈ cthickening (2 * d) (frontier (Λ ω t)),
      S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * _root_.HarmonicBalls.greenFunction (ball 0 ρ) 0 x) ≤ q}
  have hmesh' := (probTendsToOne_compl_union_iff S.P
    {ω | t < clusterExitTime (Λ ω) ρ} _).2 (hmesh t δ q ht hδ hq O hO hO' hdist)
  have hsmall := probTendsToOne_small_cells_initial_closure 𝒮 γ hγ hγ' ρ d hρ hd Ω S hS
  have hgood : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧
      Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε → ∀ a b, S.mult ε ω a b ≠ 0 →
        (cell ε (S.η ω) a ∩ cell ε (S.η ω) b).Nonempty :=
    (hΛ.and (hS.isAreaParametrized.and (adjacentCellsMeetAeStep 𝒮 γ hγ hγ' Ω S hS))).mono
      (fun _ h => ⟨h.1, h.2.1.1, h.2.2⟩)
  apply (probTendsToOne_compl_union_iff S.P F _).1
  apply ((hmesh'.inter hsmall).inter (probTendsToOne_of_ae hgood)).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  by_cases hF : ω ∈ F
  · right
    have hbound := hω.1.1.resolve_left (by simpa using hF.1)
    apply initial_boundary_iSup_le_of_frontier_gap hε (show 0 ≤ C * (q + 2 * δ) by positivity)
      hω.2.2.1 (hω.2.1.1 t ht).1 (hω.2.2.2 ε hε)
      (hω.1.2 (Λ ω t) (coneFamily_subset_before_exit hω.2.1 ht hF.1)) hF.2.1 hF.2.2 hbound
  · exact Or.inl hF

end MatedCRT.Sec7
