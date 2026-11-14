import MatedCRT.FirstPass.Derived.ConeUnstoppedWalkFamily
import MatedCRT.FirstPass.Derived.ConeScaledStoppedLaw
import LatticeProb.Analysis.ReciprocalMesh

/-! # Reciprocal mesh scaling of whole embedded walk families -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped NNReal

/-- At a reciprocal integer mesh, all starting positions and whole-walk laws
scale pathwise; the rescaled family also has the original joint law. -/
theorem MatedCRTEnv.IsValid.reciprocal_walkVertexFamily_scaling
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (lam m : ℝ≥0) :
    let n := ⌈ε⁻¹⌉₊
    let b := (n : ℝ) * ε
    0 < n ∧ b ∈ Ico (1 : ℝ) 2 ∧ ε / b = (n : ℝ)⁻¹ ∧
    (∀ ω, 0 < coneScaleRadius γ (S.hcirc ω) b → ∀ a,
      let R := coneScaleRadius γ (S.hcirc ω) b
      let η' := fun s => (R : ℂ)⁻¹ * S.η ω (b * s)
      vertexPoint ε (S.η ω) a = (R : ℂ) * vertexPoint (n : ℝ)⁻¹ η' a ∧
      (srwLaw (bmEdgeCount ε (fun t => (S.bm ω t).1)
        (fun t => (S.bm ω t).2)) a).map
        (interpPathCM (vertexPoint ε (S.η ω)) (lam * m).coe_nonneg) =
      (srwLaw (bmEdgeCount (n : ℝ)⁻¹
        (fun t => (rescaledPair b (S.bm ω) t).1)
        (fun t => (rescaledPair b (S.bm ω) t).2)) a).map
        (fun X => (⟨fun t => (R : ℂ) *
          interpPathCM (vertexPoint (n : ℝ)⁻¹ η') m.coe_nonneg X (lam * t),
          by fun_prop⟩ : C(ℝ≥0, ℂ)))) ∧
    S.P.map (fun ω => walkVertexFamily (n : ℝ)⁻¹
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) m) =
    S.P.map (fun ω => walkVertexFamily (n : ℝ)⁻¹ (S.η ω) (S.bm ω) m) := by
  dsimp only
  have hn := LatticeProb.reciprocal_mesh_eq hε
  have hb := LatticeProb.reciprocal_mesh_scale_mem hε hε1
  have hbpos : 0 < (⌈ε⁻¹⌉₊ : ℝ) * ε := lt_of_lt_of_le (by norm_num) hb.1
  refine ⟨hn.1, hb, hn.2, ?_, ?_⟩
  · intro ω hR a
    let R := coneScaleRadius γ (S.hcirc ω) ((⌈ε⁻¹⌉₊ : ℝ) * ε)
    let η' := fun s => (R : ℂ)⁻¹ * S.η ω (((⌈ε⁻¹⌉₊ : ℝ) * ε) * s)
    have hv : ∀ k, vertexPoint ε (S.η ω) k = (R : ℂ) *
        vertexPoint (⌈ε⁻¹⌉₊ : ℝ)⁻¹ η' k := by
      intro k
      have h := ConeScaledWalkData.vertexPoint_eq_mul_rescale (ε := ε) hbpos
        (Complex.ofReal_ne_zero.2 hR.ne') (S.η ω) η' (fun _ => rfl) k
      rw [hn.2] at h
      exact h
    refine ⟨hv a, ?_⟩
    have hlaw := ConeScaledWalkData.srwLaw_rescale (ε := ε) hbpos
      (inv_pos.mpr (Real.sqrt_pos.2 hbpos))
      (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
      (fun t => (rescaledPair ((⌈ε⁻¹⌉₊ : ℝ) * ε) (S.bm ω) t).1)
      (fun t => (rescaledPair ((⌈ε⁻¹⌉₊ : ℝ) * ε) (S.bm ω) t).2)
      (fun s => by simp [rescaledPair_apply])
      (fun s => by simp [rescaledPair_apply]) a
    rw [hn.2] at hlaw
    rw [← hlaw]
    congr 1
    funext X
    ext t
    exact StoppedWalkScaling.interpPathCM_scale R _ _ hv lam m X t
  · exact hS.map_walkVertexFamily_rescaled hγ hγ2 hbpos _ m

end MatedCRT
