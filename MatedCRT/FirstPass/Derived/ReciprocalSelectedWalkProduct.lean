import MatedCRT.FirstPass.Derived.ContinuousReciprocalSelectedWalk

/-! # Simultaneous reciprocal scaling of selected walk laws -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- One full-measure event supports reciprocal scaling for all shifts and marked points. -/
theorem MatedCRTEnv.IsValid.ae_forall_shiftedSelectedWalkLaw_reciprocal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ ω ∂S.P, ∀ (θ : ℝ) (m : ℝ≥0) (x : ℂ),
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      let R : ℂ := (coneScaleRadius γ (S.hcirc ω) q : ℝ)
      let η' : ℝ → ℂ := fun t => R⁻¹ * S.η ω (q * t)
      let w' := rescaledPair q (S.bm ω)
      shiftedSelectedWalkLaw δ m (δ * θ) x η' w' =
        (shiftedSelectedWalkLaw b m (b * θ) (R * x) (S.η ω) (S.bm ω)).map
          (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) := by
  obtain ⟨hn, _⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  filter_upwards [hS.ae_coneScaleRadius_pos_from_coupling hγ hγ2
    ((⌊b⁻¹⌋₊ : ℝ) * b)] with ω hR
  intro θ m x
  have hR' : ((coneScaleRadius γ (S.hcirc ω) ((⌊b⁻¹⌋₊ : ℝ) * b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hR.ne'
  exact shiftedSelectedWalkLaw_reciprocal_floor_mesh hb hb1
    (inv_pos.mpr (Real.sqrt_pos.mpr hq)) hR' θ (S.bm ω)
    (rescaledPair ((⌊b⁻¹⌋₊ : ℝ) * b) (S.bm ω))
    (by
      intro t
      apply Prod.ext <;> simp only [rescaledPair_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul])
    (S.η ω)
    (fun t => ((coneScaleRadius γ (S.hcirc ω) ((⌊b⁻¹⌋₊ : ℝ) * b) : ℝ) : ℂ)⁻¹ *
      S.η ω (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (by intro t; rfl) m x

/-- Reciprocal scaling holds jointly almost everywhere for an independent shift. -/
theorem MatedCRTEnv.IsValid.ae_prod_shiftedSelectedWalkLaw_reciprocal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1)
    (Q : Measure ℝ) [SFinite Q] (m : ℝ≥0) (x : ℂ) :
    ∀ᵐ p ∂Q.prod S.P,
      let θ := p.1
      let ω := p.2
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      let R : ℂ := (coneScaleRadius γ (S.hcirc ω) q : ℝ)
      let η' : ℝ → ℂ := fun t => R⁻¹ * S.η ω (q * t)
      let w' := rescaledPair q (S.bm ω)
      shiftedSelectedWalkLaw δ m (δ * θ) x η' w' =
        (shiftedSelectedWalkLaw b m (b * θ) (R * x) (S.η ω) (S.bm ω)).map
          (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (hS.ae_forall_shiftedSelectedWalkLaw_reciprocal hγ hγ2 hb hb1)] with p hp
  exact hp p.1 m x

end MatedCRT
