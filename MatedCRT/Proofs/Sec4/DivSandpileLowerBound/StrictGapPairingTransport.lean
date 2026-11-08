import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapConeAssembly
import Mathlib.Probability.Process.FiniteDimensionalLaws

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

/-- The coordinate representation may hold almost surely separately for each
zero-mean test. Equality of finite-dimensional distributions then gives equality
of the full joint pairing laws, even for an uncountable test-function space. -/
theorem localModConstPairings_shift_laws_of_coordinate_modification
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → I → ℝ) (d : I → ℝ) (hX : Measurable X)
    (hshift : P.map (fun ω i => X ω i + d i) ≪ P.map X ∧
      P.map X ≪ P.map (fun ω i => X ω i + d i))
    (hC : Ω → (ℂ → ℝ) → ℝ) (g : ℂ → ℝ) (α : ℝ) (U : Set ℂ)
    (i : LocalZeroMeanTest U → I)
    (hfieldm : ∀ φ : LocalZeroMeanTest U, Measurable (fun ω => hC ω φ.1))
    (hfield : ∀ φ : LocalZeroMeanTest U, ∀ᵐ ω ∂P, hC ω φ.1 = X ω (i φ))
    (hpair : ∀ φ, (∫ x, g x * φ.1 x) = d (i φ)) :
    P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) ≪
        P.map (localModConstPairings α hC U) ∧
      P.map (localModConstPairings α hC U) ≪
        P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) := by
  let Y : Ω → I → ℝ := fun ω j => X ω j + d j
  let R : (I → ℝ) → LocalZeroMeanTest U → ℝ := fun v φ =>
    v (i φ) - α * ∫ x, φ.1 x * Real.log ‖x‖
  let Z := localModConstPairings α hC U
  let W := localModConstPairings α (fun ω => addFunPairing (hC ω) g) U
  have hY : Measurable Y := measurable_pi_iff.mpr fun j =>
    ((measurable_pi_apply j).comp hX).add_const _
  have hR : Measurable R := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply (i φ)).sub_const _
  have hZ : Measurable Z := measurable_pi_iff.mpr fun φ =>
    (hfieldm φ).sub_const _
  have hW : Measurable W := measurable_pi_iff.mpr fun φ =>
    ((hfieldm φ).add_const _).sub_const _
  have hZX : P.map Z = P.map (R ∘ X) := by
    apply ProbabilityTheory.map_eq_of_forall_ae_eq hZ.aemeasurable (hR.comp hX).aemeasurable
    intro φ
    filter_upwards [hfield φ] with ω hω
    simp only [R, localModConstPairings, fieldPairing, Function.comp_apply, hω]
  have hWY : P.map W = P.map (R ∘ Y) := by
    apply ProbabilityTheory.map_eq_of_forall_ae_eq hW.aemeasurable (hR.comp hY).aemeasurable
    intro φ
    filter_upwards [hfield φ] with ω hω
    simp only [R, Y, localModConstPairings, fieldPairing, addFunPairing,
      Function.comp_apply, hω, hpair]
  have hf := hshift.1.map hR
  have hb := hshift.2.map hR
  rw [Measure.map_map hR hY, Measure.map_map hR hX, ← hWY, ← hZX] at hf hb
  exact ⟨hf, hb⟩

end MatedCRT
