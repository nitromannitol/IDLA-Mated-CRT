import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw

/-! # Continuous-path scaling of selected Brownian-edge walks -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Reciprocal mesh scaling of the selected continuous-path walk law. -/
theorem shiftedSelectedWalkLaw_reciprocal_floor_mesh
    {b c : ℝ} (hb : 0 < b) (hb1 : b < 1) (hc : 0 < c)
    {R : ℂ} (hR : R ≠ 0) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t =
      (c * (w (((⌊b⁻¹⌋₊ : ℝ) * b) * t)).1,
       c * (w (((⌊b⁻¹⌋₊ : ℝ) * b) * t)).2))
    (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (m : ℝ≥0) (x : ℂ) :
    (srwLaw (bmEdgeCount ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => (w' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)).1)
        (fun t => (w' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)).2))
        (vertexOf ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
          (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) x)).map
      (interpPathCM (vertexPoint ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ))) m.coe_nonneg) =
    ((srwLaw (bmEdgeCount b (fun t => (w (t + b * θ)).1)
        (fun t => (w (t + b * θ)).2))
        (vertexOf b (fun t => η (t + b * θ)) (R * x))).map
      (interpPathCM (vertexPoint b (fun t => η (t + b * θ))) m.coe_nonneg)).map
        (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) := by
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  rw [vertexOf_reciprocal_floor_mesh hb hb1 hR θ η η' hη x, ← hmesh,
    srwLaw_shiftedPhysical_rescale hq hc θ w w' hw]
  have hscale : Measurable (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hscale (measurable_interpPathCM _ m.coe_nonneg)]
  congr 1
  funext ξ
  ext t
  simpa only [ContinuousMap.mul_apply, ContinuousMap.const_apply, Function.comp_apply, interpPathCM_vertexPoint] using
    interpolatedWalk_shiftedPhysical_rescale hq θ R η η' hη m ξ t

/-- In a valid cone environment, the original marked point is the radius multiple
of the marked point in the rescaled environment. -/
theorem MatedCRTEnv.IsValid.ae_shiftedSelectedWalkLaw_reciprocal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1)
    (θ : ℝ) (m : ℝ≥0) (x : ℂ) :
    ∀ᵐ ω ∂S.P,
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      let R : ℂ := (coneScaleRadius γ (S.hcirc ω) q : ℝ)
      let η' : ℝ → ℂ := fun t => R⁻¹ * S.η ω (q * t)
      let w' := rescaledPair q (S.bm ω)
      shiftedSelectedWalkLaw δ m (δ * θ) x η' w' =
        (shiftedSelectedWalkLaw b m (b * θ) (R * x) (S.η ω) (S.bm ω)).map
          (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) := by
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  filter_upwards [hS.ae_coneScaleRadius_pos_from_coupling hγ hγ2
    ((⌊b⁻¹⌋₊ : ℝ) * b)] with ω hR
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

end MatedCRT
