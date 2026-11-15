import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkConeScale

/-! # Paper walk witnesses at real cone masses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology ProbabilityTheory
open LatticeProb MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal NNReal

namespace MatedCRT

/-- The physical-walk witness estimate holds as the positive mass tends to zero,
provided the varying environment laws are uniformly absolutely continuous. -/
theorem tendsto_measure_paperWalk_witness_at_coneScale_real
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure JointShiftedWalkEnvironment) [IsFiniteMeasure ν]
    (X : ℝ → Ω → JointShiftedWalkEnvironment)
    {γ α : ℝ} (hγ : 0 < γ) (hα : α < lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞)
    (a : ℕ → ℝ) (ha : Antitone a) (ha_pos : ∀ k, 0 < a k)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        totalizedShiftedPhysicalWalkLaw e.2.1.2.1 e.2.1.2.2 e.1 j
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t))
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ b in 𝓝[>] (0 : ℝ), ∀ T : Set JointShiftedWalkEnvironment,
        NullMeasurableSet T ν → ν T ≤ d → P ((X b) ⁻¹' T) ≤ e) :
    Tendsto (fun b => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf
        (X b ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) b, j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X b ω).2.1.2.1 (X b ω).2.1.2.2 (X b ω).1 j
        {ξ | (jointShiftedWalkWitnessOf
          (X b ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) b, j),
          scaledWalkPath (jointShiftedWalkWitnessOf
            (X b ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) b, j)).2 ξ) ∈ U} ≤ t})
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_iff_seq_tendsto.2
  intro b hb
  apply tendsto_measure_paperWalk_witness_at_coneScale P ν (fun n => X (b n))
    hγ hα hB hB' b hb hU hK t a ha ha_pos ha_small hgood hmesh
  intro e he
  obtain ⟨d, hd, h⟩ := hcont e he
  exact ⟨d, hd, hb.eventually h⟩

end MatedCRT
