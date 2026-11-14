import MatedCRT.FirstPass.Derived.ConeScaledStoppedLaw
import MatedCRT.FirstPass.Derived.ConeStoppedWalkJointLaw
import LatticeProb.Analysis.ReciprocalMesh

/-! # Reciprocal mesh scaling of stopped walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRT.ExitCouplingGlue

/-- A positive mesh below one can be rescaled to a reciprocal integer mesh. The
stopped law rescales pathwise, and the rescaled quenched law has the same
distribution as the original quenched law at that reciprocal mesh. -/
theorem MatedCRTEnv.IsValid.reciprocal_stoppedWalk_scaling {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ρ : ℝ) (lam m : ℝ≥0) (a : ℤ) :
    let n := ⌈ε⁻¹⌉₊
    let b := (n : ℝ) * ε
    0 < n ∧ b ∈ Ico (1 : ℝ) 2 ∧ ε / b = (n : ℝ)⁻¹ ∧
    (∀ ω, 0 < coneScaleRadius γ (S.hcirc ω) b →
      (srwLaw (bmEdgeCount ε (fun t => (S.bm ω t).1)
        (fun t => (S.bm ω t).2)) a).map
        (stoppedInterp (vertexPoint ε (S.η ω)) (lam * m)
          (interiorCellVertices ε (S.η ω)
            (ball (0 : ℂ) (coneScaleRadius γ (S.hcirc ω) b * ρ)))) =
      (srwLaw (bmEdgeCount (n : ℝ)⁻¹
        (fun t => (rescaledPair b (S.bm ω) t).1)
        (fun t => (rescaledPair b (S.bm ω) t).2)) a).map
        (fun X => (⟨fun t => (coneScaleRadius γ (S.hcirc ω) b : ℂ) *
          stoppedInterp (vertexPoint (n : ℝ)⁻¹ (fun s =>
            (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))) m
            (interiorCellVertices (n : ℝ)⁻¹ (fun s =>
              (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
              (ball (0 : ℂ) ρ)) X (lam * t), by fun_prop⟩ : C(ℝ≥0, ℂ)))) ∧
    S.P.map (fun ω =>
      (srwLaw (bmEdgeCount (n : ℝ)⁻¹ (fun t => (rescaledPair b (S.bm ω) t).1)
        (fun t => (rescaledPair b (S.bm ω) t).2)) a).map
        (stoppedInterp (vertexPoint (n : ℝ)⁻¹ (fun s =>
          (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))) m
          (interiorCellVertices (n : ℝ)⁻¹ (fun s =>
            (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
            (ball (0 : ℂ) ρ)))) =
    S.P.map (fun ω =>
      (srwLaw (bmEdgeCount (n : ℝ)⁻¹ (fun t => (S.bm ω t).1)
        (fun t => (S.bm ω t).2)) a).map
        (stoppedInterp (vertexPoint (n : ℝ)⁻¹ (S.η ω)) m
          (interiorCellVertices (n : ℝ)⁻¹ (S.η ω) (ball (0 : ℂ) ρ)))) := by
  dsimp only
  have hn := LatticeProb.reciprocal_mesh_eq hε
  have hb := LatticeProb.reciprocal_mesh_scale_mem hε hε1
  have hbpos : 0 < (⌈ε⁻¹⌉₊ : ℝ) * ε := lt_of_lt_of_le (by norm_num) hb.1
  refine ⟨hn.1, hb, hn.2, ?_, ?_⟩
  · intro ω hR
    have hs := ConeScaledWalkData.stoppedInterp_law_rescale (ε := ε) hbpos
      (inv_pos.mpr (Real.sqrt_pos.2 hbpos)) hR
      (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
      (fun t => (rescaledPair ((⌈ε⁻¹⌉₊ : ℝ) * ε) (S.bm ω) t).1)
      (fun t => (rescaledPair ((⌈ε⁻¹⌉₊ : ℝ) * ε) (S.bm ω) t).2)
      (fun s => by simp [rescaledPair_apply])
      (fun s => by simp [rescaledPair_apply])
      (S.η ω) (fun s => (coneScaleRadius γ (S.hcirc ω) ((⌈ε⁻¹⌉₊ : ℝ) * ε) : ℂ)⁻¹ *
        S.η ω (((⌈ε⁻¹⌉₊ : ℝ) * ε) * s)) (fun _ => rfl) ρ lam m a
    rw [hn.2] at hs
    exact hs
  · exact hS.map_stoppedWalkLaw_rescaled hγ hγ2 hbpos _ _ (Or.inl isOpen_ball) m a

end MatedCRT
