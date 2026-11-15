import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkBadMesh
import LatticeProb.LQG.JointShiftedWalkConeScaleMesh

/-! # Paper walk witnesses at cone scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology ProbabilityTheory
open LatticeProb MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal NNReal

namespace MatedCRT

/-- Good radii for the physical walk transfer to cone-scale witnesses when
varying environment laws are uniformly absolutely continuous. -/
theorem tendsto_measure_paperWalk_witness_at_coneScale
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure JointShiftedWalkEnvironment) [IsFiniteMeasure ν]
    (X : ℕ → Ω → JointShiftedWalkEnvironment)
    {γ α : ℝ} (hγ : 0 < γ) (hα : α < lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝[>] 0))
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
      ∀ᶠ n in atTop, ∀ T : Set JointShiftedWalkEnvironment,
        NullMeasurableSet T ν → ν T ≤ d → P ((X n) ⁻¹' T) ≤ e) :
    Tendsto (fun n => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf
        (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X n ω).2.1.2.1 (X n ω).2.1.2.2 (X n ω).1 j
        {ξ | (jointShiftedWalkWitnessOf
          (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j),
          scaledWalkPath (jointShiftedWalkWitnessOf
            (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j)).2 ξ) ∈ U} ≤ t})
      atTop (𝓝 0) := by
  have hv := (ae_jointShiftedWalk_goodRadius_iff_paper ν hmesh U K t).2 hgood
  obtain ⟨hvertex, hbad⟩ := tendsto_jointShiftedWalk_witness_and_badMesh_at_coneScale
    P ν X hγ hα hB hB' b hb hU hK t a ha ha_pos ha_small hv hmesh hcont
  exact tendsto_measure_paperWalk_witness_of_vertex_of_badMesh P atTop X
    (fun n ω => coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n)) U K t hvertex hbad

end MatedCRT
