import MatedCRT.FirstPass.Derived.ContinuousReciprocalSelectedWalk

/-! # Joint law of reciprocal-mesh selected walks -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The reciprocal-mesh joint law retains the radius-dependent original marked point. -/
theorem MatedCRTEnv.IsValid.map_reciprocal_shiftedSelectedWalkLaw
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1)
    (θ : ℝ) (m : ℝ≥0) (x : ℂ) :
    S.P.map (fun ω =>
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let R : ℂ := (coneScaleRadius γ (S.hcirc ω) q : ℝ)
      let η' : ℝ → ℂ := fun t => R⁻¹ * S.η ω (q * t)
      let w' := rescaledPair q (S.bm ω)
      (η', w', (shiftedSelectedWalkLaw b m (b * θ) (R * x) (S.η ω) (S.bm ω)).map
        (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p))) =
    S.P.map (fun ω =>
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      (S.η ω, S.bm ω, shiftedSelectedWalkLaw δ m (δ * θ) x (S.η ω) (S.bm ω))) := by
  obtain ⟨hn, _⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  have hδ : 0 < (⌊b⁻¹⌋₊ : ℝ)⁻¹ := by positivity
  refine (Measure.map_congr ?_).trans
    (hS.map_shiftedSelectedWalkLaw_rescaled hγ hγ2 hq hδ m
      ((⌊b⁻¹⌋₊ : ℝ)⁻¹ * θ) x)
  filter_upwards [hS.ae_shiftedSelectedWalkLaw_reciprocal hγ hγ2 hb hb1 θ m x] with ω h
  exact congrArg (fun z => (_, _, z)) h.symm

end MatedCRT
