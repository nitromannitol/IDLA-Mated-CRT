import MatedCRT.Steps.Sec7.DivSandpileUpperBound
import MatedCRT.Proofs.Sandpile.ComponentComparison
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements

/-! Proposition 7.1 using the obstacle problem on the origin component.

The adjacent-cell contact input uses the mating-of-trees formalization of Leonardo Bonanno. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- The shell confinement step implies Proposition 7.1. The comparison uses
the component of the origin, so it does not require the whole stopping domain
to be connected. -/
theorem divSandpileUpperBound_of_confinement (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hshell : StoppedShellConfinementStep 𝒮) :
    DivSandpileUpperBoundStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  let d := min δ (ρ / 3) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d ≤ δ := by dsimp [d]; have := min_le_left δ (ρ / 3); linarith
  have hdρ : d < ρ / 3 := by dsimp [d]; have := min_le_right δ (ρ / 3); linarith
  have hadj := adjacentCellsMeetAeStep 𝒮
  have hlocal := hshell hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ d t hd (by linarith) ht
  unfold TendsToOneOn at hlocal ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlocal
    (Eventually.of_forall fun _ => zero_le) ?_
  apply eventually_nhdsWithin_of_forall
  intro ε hε
  apply measure_mono_ae
  filter_upwards [hΛ, ae_isRegularMatedMap hadj hγ hγ' hS] with ω hfam hregular
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hgood
  obtain ⟨hinterior, hfill⟩ := hgood
  have hball := hfill.trans (Sec7.outerNbhd_subset_ball_of_subset_third hρ hdρ
    (Sec7.coneFamily_subset_before_exit hfam ht hbad.1))
  have hcell0 : cell ε (S.η ω) 0 ⊆ ball 0 ρ := by
    intro z hz
    exact hball (mem_iUnion₂.mpr ⟨0, Or.inl rfl, hz⟩)
  have h0 : (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ := by
    have hnonempty : (cell ε (S.η ω) 0).Nonempty :=
      ⟨vertexPoint ε (S.η ω) 0, Sec7.vertexPoint_mem_own_cell hε.le (S.η ω) 0⟩
    obtain ⟨z, hz⟩ := hnonempty
    refine ⟨⟨z, hz, hcell0 hz⟩, ?_⟩
    rintro ⟨z, hz, hzfront⟩
    exact (disjoint_frontier_iff_isOpen.mpr isOpen_ball).le_bot ⟨hzfront, hcell0 hz⟩
  have hsubset := Sandpile.global_cluster_subset_stopped_closure_of_regular
    (hregular ε hε) ht h0 hinterior
  apply hbad.2
  intro z hz
  rcases mem_iUnion₂.mp hz with ⟨a, ha, hza⟩
  apply (cthickening_mono hdδ _ : outerNbhd d (Λ ω t) ⊆ outerNbhd δ (Λ ω t))
  exact hfill (mem_iUnion₂.mpr ⟨a, hsubset ha, hza⟩)

/-- Proposition 7.1 from the shell iteration and the corrected numbered inputs. -/
theorem divSandpileUpperBound_of_shellIteration (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hiteration : ShellIterationStep 𝒮) :
    DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_confinement 𝒮 hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude
    (stoppedShellConfinement_of_intermediateShell 𝒮 (intermediateShell_of_shellIteration 𝒮 hiteration))

end MatedCRT
