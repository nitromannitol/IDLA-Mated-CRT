import MatedCRT.FirstPass.Derived.ConeReciprocalIndependentShiftLaw

/-! # Limits of joint laws under reciprocal mesh scaling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Filter Set
open scoped NNReal Topology

/-- A limit of an observable of the joint law along reciprocal integer meshes
transfers to the corresponding rescaled joint law at positive real meshes.
The original walk is started at the radius-dependent point. -/
theorem MatedCRTEnv.IsValid.tendsto_reciprocal_selected_walk_prod
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (Q : Measure ℝ) [SFinite Q] (m : ℝ≥0) (x : ℂ)
    {α : Type} [TopologicalSpace α]
    (Φ : Measure (ℝ × ((ℝ → ℂ) × C(ℝ, ℝ × ℝ) × Measure C(ℝ≥0, ℂ))) → α)
    {a : α}
    (hlim : Tendsto (fun n : ℕ => Φ ((Q.prod S.P).map (fun p =>
      (p.1, (S.η p.2, S.bm p.2,
        shiftedSelectedWalkLaw (n : ℝ)⁻¹ m ((n : ℝ)⁻¹ * p.1) x
          (S.η p.2) (S.bm p.2)))))) atTop (𝓝 a)) :
    Tendsto (fun b : ℝ => Φ ((Q.prod S.P).map (fun p =>
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let R : ℂ := (coneScaleRadius γ (S.hcirc p.2) q : ℝ)
      let η : ℝ → ℂ := fun t => R⁻¹ * S.η p.2 (q * t)
      (p.1, (η, rescaledPair q (S.bm p.2),
        (shiftedSelectedWalkLaw b m (b * p.1) (R * x) (S.η p.2) (S.bm p.2)).map
          (fun z : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * z))))))
      (𝓝[>] 0) (𝓝 a) := by
  have hcomp := hlim.comp LatticeProb.tendsto_reciprocal_floor_mesh_index
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left] with b hb hb1
  exact congrArg Φ (hS.map_reciprocal_selected_walk_prod hγ hγ2 hb hb1 Q m x).symm

end MatedCRT
