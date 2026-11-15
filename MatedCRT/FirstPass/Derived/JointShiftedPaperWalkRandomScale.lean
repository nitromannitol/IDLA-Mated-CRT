import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkTransfer

/-! # Paper walk witnesses at random scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LatticeProb MatedCRTHarmonic
open scoped ENNReal NNReal

namespace MatedCRT

/-- Under a common environment law, good small radii transfer to the physical
walk at almost surely positive random scales with vanishing tails. -/
theorem tendsto_measure_paperWalk_witness_at_ae_positive_random_scale
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure JointShiftedWalkEnvironment) [IsFiniteMeasure ν]
    (l : Filter ι) (X : ι → Ω → JointShiftedWalkEnvironment) (R : ι → Ω → ℝ)
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞)
    (a : ℕ → ℝ) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
    (hgood : ∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        totalizedShiftedPhysicalWalkLaw e.2.1.2.1 e.2.1.2.2 e.1 j
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t))
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, Measure.map (X i) P = ν)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X i ω).2.1.2.1 (X i ω).2.1.2.2 (X i ω).1 j
        {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t})
      l (𝓝 0) := by
  let R' : ι → Ω → ℝ := fun i ω => if 0 < R i ω then R i ω else 1
  have hR'eq (i : ι) : ∀ᵐ ω ∂P, R' i ω = R i ω := by
    filter_upwards [hR i] with ω hω
    simp [R', hω]
  have hR'pos (i : ι) (ω : Ω) : 0 < R' i ω := by
    dsimp only [R']
    split_ifs with h
    · exact h
    · exact zero_lt_one
  have hscale' (k : ℕ) : Tendsto (fun i => P {ω | a k < R' i ω}) l (𝓝 0) := by
    have heq : (fun i => P {ω | a k < R' i ω}) =
        (fun i => P {ω | a k < R i ω}) := by
      funext i
      apply measure_congr
      filter_upwards [hR'eq i] with ω hω
      simp only [hω]
    rw [heq]
    exact hscale k
  have hgood' := (ae_jointShiftedWalk_goodRadius_iff_paper ν hmesh U K t).2 hgood
  have hlimit := tendsto_measure_jointShiftedWalk_witness_at_random_scale
    P ν l X R' hU hK t a ha ha_small hgood' hX hlaw hR'pos hscale'
  have heq (i : ι) :
      P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R' i ω, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X i ω, R' i ω, j))
          {ξ | (jointShiftedWalkWitnessOf (X i ω, R' i ω, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R' i ω, j)).2 ξ) ∈ U} ≤ t} =
      P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
        totalizedShiftedPhysicalWalkLaw (X i ω).2.1.2.1 (X i ω).2.1.2.2 (X i ω).1 j
          {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t} := by
    rw [measure_jointShiftedWalk_witness_eq_paper P ν (X i) (hX i) (hlaw i) hmesh
      (R' i) U K t]
    apply measure_congr
    filter_upwards [hR'eq i] with ω hω
    simp only [hω]
  simp_rw [heq] at hlimit
  exact hlimit

end MatedCRT
