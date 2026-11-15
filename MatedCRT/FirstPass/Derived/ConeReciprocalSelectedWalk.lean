import MatedCRT.FirstPass.Derived.ConeEnvironmentJointLaw
import MatedCRT.FirstPass.Derived.BrownianWalkReciprocalSelector

/-! # Reciprocal mesh scaling for a selected walk in a quantum cone -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The cone radius is almost surely positive for a valid environment. -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_pos_from_coupling
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (q : ℝ) :
    ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) q := by
  obtain ⟨V, hV, hC, hbm, htie⟩ := hS.exists_couplingData_tied
  filter_upwards [hS.ae_coneScaleRadius_eq_coneScaleOfPair hγ hγ2 hC
    (htie.mono fun _ h => h.2) q] with ω hω
  rw [hω]
  exact Real.exp_pos _

/-- At reciprocal floor mesh, cone rescaling transports the selected Brownian-edge
walk law and sends the marked point to its radius multiple. -/
theorem MatedCRTEnv.IsValid.ae_reciprocal_selectedBrownianWalk_rescaled
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1)
    (θ speed : ℝ) (x : ℂ) :
    ∀ᵐ ω ∂S.P,
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      let R : ℂ := (coneScaleRadius γ (S.hcirc ω) q : ℝ)
      let η' : ℝ → ℂ := fun t => R⁻¹ * S.η ω (q * t)
      let w' := rescaledPair q (S.bm ω)
      (srwLaw (bmEdgeCount δ (fun t => (w' (t + δ * θ)).1)
          (fun t => (w' (t + δ * θ)).2))
          (vertexOf δ (fun t => η' (t + δ * θ)) x)).map
        (interpolatedWalk δ (fun t => η' (t + δ * θ)) speed) =
      ((srwLaw (bmEdgeCount b (fun t => (S.bm ω (t + b * θ)).1)
          (fun t => (S.bm ω (t + b * θ)).2))
          (vertexOf b (fun t => S.η ω (t + b * θ)) (R * x))).map
        (interpolatedWalk b (fun t => S.η ω (t + b * θ)) speed)).map
          (fun p t => R⁻¹ * p t) := by
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  filter_upwards [hS.ae_coneScaleRadius_pos_from_coupling hγ hγ2
    ((⌊b⁻¹⌋₊ : ℝ) * b)] with ω hR
  have hR' : ((coneScaleRadius γ (S.hcirc ω) ((⌊b⁻¹⌋₊ : ℝ) * b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hR.ne'
  exact interpolatedBrownianWalkLaw_reciprocal_floor_mesh_vertexOf hb hb1
    (inv_pos.mpr (Real.sqrt_pos.mpr hq)) hR' θ (S.bm ω)
    (rescaledPair ((⌊b⁻¹⌋₊ : ℝ) * b) (S.bm ω))
    (by
      intro t
      apply Prod.ext <;> simp only [rescaledPair_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul])
    (S.η ω)
    (fun t => ((coneScaleRadius γ (S.hcirc ω) ((⌊b⁻¹⌋₊ : ℝ) * b) : ℝ) : ℂ)⁻¹ *
      S.η ω (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (by intro t; rfl) speed x

end MatedCRT
