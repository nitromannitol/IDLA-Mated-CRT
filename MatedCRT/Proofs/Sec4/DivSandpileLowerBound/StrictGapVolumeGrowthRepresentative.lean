import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapOdometerDecoder
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRepresentative
import HarmonicBalls.Proofs.Sec3.ConservationOfMass

/-! Measurable regularization defects for measures with volume growth. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- The measurable defect event represents the cluster defect of any locally
finite measure satisfying volume growth, using only its restriction to the disc. -/
theorem exists_measurable_restricted_cluster_regularity_defect
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν →
      (∃ βm βp : ℝ, VolumeGrowth ν R βm βp) →
      (ν.restrict (ball 0 R) ∈ E ↔ ν ∈ confinedRegularizationDefect R t z) := by
  obtain ⟨E, hE, hgood⟩ := exists_measurable_nonCoincidence_regularity_defect (t := t) (z := z) hR
  refine ⟨E, hE, ?_⟩
  intro ν hν ⟨βm, βp, hV⟩
  have hpot : ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) :=
    greenPotentialBallContinuousStep_holds ν hν R βm βp hR hV
  obtain ⟨_, hvcont, hclass, _, _⟩ :=
    obstacleLeastSuperharmonicMajorantGeneral_holds ν hν R βm βp hR hV z hz t ht
  have hopen := isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hν hR hV hz ht
  have hβcont := continuousOn_obstacle (t := t) greenFunctionBall hR hz hpot
  have hodcont : ContinuousOn (shiftedOdometer ν R z t) (ball (0 : ℂ) R \ {z}) := by
    have hsub : ball (0 : ℂ) R \ {z} ⊆ closedBall 0 R \ {z} :=
      fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
    exact (hvcont.mono (hsub.trans sdiff_subset)).sub (hβcont.mono hsub)
  have hpot_eq : greenPotentialBall (ν.restrict (ball 0 R)) R = greenPotentialBall ν R := by
    funext x
    simp only [greenPotentialBall, Measure.restrict_restrict measurableSet_ball, inter_self]
  have hclass_eq : shiftedSupersolutions (ν.restrict (ball 0 R)) R z t = shiftedSupersolutions ν R z t := by
    simp only [shiftedSupersolutions, obstacle, hpot_eq]
  have hod_eq : shiftedOdometer (ν.restrict (ball 0 R)) R z t = shiftedOdometer ν R z t := by
    funext x
    simp only [shiftedOdometer, shiftedLeastSupersolution, hclass_eq, obstacle, hpot_eq]
  have hnon_eq := nonCoincidenceSet_eq_restrict_ball ν R t z
  have hcluster := cluster_eq_nonCoincidenceSet_of_greenPotential (z := z) hν ht.le hpot
    (greenPotentialBallLaplacianStep_holds ν hν R βm βp hR hV)
  have hresult := hgood (ν.restrict (ball 0 R)) (hpot_eq ▸ hpot)
    (hclass_eq ▸ ⟨_, hclass⟩) (hnon_eq ▸ hopen) (hod_eq ▸ hodcont)
  simpa only [← hnon_eq, ← hcluster, confinedRegularizationDefect, mem_ofPred_eq] using hresult

/-- Fixed-time regularization under a restricted mass-shift law, when the
positive mass shifts preserve local finiteness and volume growth. -/
theorem ae_no_regularization_defect_of_scaled_volumeGrowth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P) {R t γ : ℝ} {z : ℂ}
    (hR : 0 < R) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 R)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) R βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) R z s) ⊆ ball 0 R →
        μ ω (frontier (cluster (μ ω) R z s)) = 0)
    (hscaled : ∀ᵐ ω ∂P, ∀ c : ℝ,
      IsLocallyFiniteMeasure (ENNReal.ofReal (Real.exp (γ * c)) • μ ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (ENNReal.ofReal (Real.exp (γ * c)) • μ ω) R βm βp)
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 R)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 R)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) R z t) ⊆ ball 0 R →
      interior (closure (cluster (μ ω) R z t)) = cluster (μ ω) R z t := by
  obtain ⟨E, hE, hgood⟩ := exists_measurable_restricted_cluster_regularity_defect hR hz ht
  apply ae_no_regularization_defect_of_ae_measurable_representative P μ hμm hR ht hγ hz hregular E hE
  · filter_upwards [hscaled] with ω hω
    intro c
    obtain ⟨hlocal, hvolume⟩ := hω c
    simpa only [Measure.restrict_smul] using hgood _ hlocal hvolume
  · exact hlaw

end MatedCRT
