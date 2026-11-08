import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapConeAssembly

/-! # Transport of field shift laws to local zero-mean pairings -/

namespace MatedCRT

open MeasureTheory Set _root_.HarmonicBalls

/-- A measurable coordinate representation transports equivalence of field
shift laws to the joint law of local zero-mean pairings. The representation
must identify both the field and the deterministic smooth-shift pairings. -/
theorem localModConstPairings_shift_laws_of_coordinate_representation
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → I → ℝ) (d : I → ℝ) (hX : Measurable X)
    (hshift : P.map (fun ω i => X ω i + d i) ≪ P.map X ∧
      P.map X ≪ P.map (fun ω i => X ω i + d i))
    (hC : Ω → (ℂ → ℝ) → ℝ) (g : ℂ → ℝ) (α : ℝ) (U : Set ℂ)
    (i : LocalZeroMeanTest U → I)
    (hfield : ∀ ω φ, hC ω φ.1 = X ω (i φ))
    (hpair : ∀ φ, (∫ x, g x * φ.1 x) = d (i φ)) :
    P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) ≪
        P.map (localModConstPairings α hC U) ∧
      P.map (localModConstPairings α hC U) ≪
        P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) := by
  let Y : Ω → I → ℝ := fun ω j => X ω j + d j
  let R : (I → ℝ) → LocalZeroMeanTest U → ℝ := fun v φ =>
    v (i φ) - α * ∫ x, φ.1 x * Real.log ‖x‖
  have hY : Measurable Y := measurable_pi_iff.mpr fun j =>
    ((measurable_pi_apply j).comp hX).add_const _
  have hR : Measurable R := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply (i φ)).sub_const _
  have hRX : R ∘ X = localModConstPairings α hC U := by
    funext ω φ
    simp only [Function.comp_apply, R, localModConstPairings, fieldPairing]
    rw [hfield]
  have hRY : R ∘ Y = localModConstPairings α (fun ω => addFunPairing (hC ω) g) U := by
    funext ω φ
    simp only [Function.comp_apply, R, Y, localModConstPairings, fieldPairing, addFunPairing]
    rw [hfield, hpair]
  have hf := hshift.1.map hR
  have hb := hshift.2.map hR
  rw [Measure.map_map hR hY, Measure.map_map hR hX, hRY, hRX] at hf hb
  exact ⟨hf, hb⟩

end MatedCRT
