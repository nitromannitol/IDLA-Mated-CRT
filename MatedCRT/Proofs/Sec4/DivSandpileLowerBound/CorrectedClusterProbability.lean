import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.CorrectedClusterRegular
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ComponentReduction
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Interior

/-! The corrected cluster identity on the shell-localization event. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- Shell confinement gives the corrected stopped/global cluster identity in
    probability before the continuum exit time. -/
theorem clusterIdentity_on_exitEvent_of_shellConfinement
    (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hshell : StoppedShellConfinementStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      sandpileCluster (S.mult ε ω) (t / ε) = vClosure (S.mult ε ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
  let d := ρ / 6
  have hd : 0 < d := by dsimp [d]; positivity
  have hdρ : d < ρ / 3 := by dsimp [d]; linarith
  have hadj := adjacentCellsMeetAeStep 𝒮
  have hlocal := hshell hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ d t hd (by linarith) ht
  unfold TendsToOneOn at hlocal ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlocal
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht)] with ε hε hεt
  apply measure_mono_ae
  filter_upwards [hΛ, ae_isRegularMatedMap hadj hγ hγ2 hS] with ω hfam hregular
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
  exact hbad.2 (sandpileCluster_eq_matedDiscreteCluster_closure_of_regular
    (hregular ε hε) hεt h0 hinterior)

end MatedCRT

#print axioms MatedCRT.clusterIdentity_on_exitEvent_of_shellConfinement
