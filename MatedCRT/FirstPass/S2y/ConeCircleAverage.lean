import MatedCRT.Steps.Sec2.LQGMeasureProperties
import MatedCRT.Defs.QuantumCone
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Cone circle averages are local

Reduction of `ConeCircleAverageLocalityStep` (MatedCRT/Steps/Sec2/LQGMeasureProperties.lean:58) to an
absolute approximation of the circle average by pairings with test functions supported in `U`
(Duplantier–Sheffield, arXiv:0808.1560v2, Section 3.1, the mollified uniform circle measure).

* `measurable_fieldPairing_zero_of_test`: a pairing with a test function supported in `U` is
  `fieldSigmaAlgebra 0 hC U`-measurable.
* `exists_fieldSigma_version_of_tendstoInMeasure`: an in-probability limit of such pairings has an almost surely
  equal `fieldSigmaAlgebra 0 hC U`-measurable version (a.s. convergent subsequence, then `limsup`).
* `coneCircleAverageLocalityStep_of_absApprox`: the Step follows from the absolute approximation hypothesis `hAbs`,
  which is NOT proved in this file.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- A pairing with a test function supported in `U` is `fieldSigmaAlgebra 0 hC U`-measurable. -/
theorem measurable_fieldPairing_zero_of_test {Ω : Type} [MeasurableSpace Ω] (hC : Ω → (ℂ → ℝ) → ℝ)
    (U : Set ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction U φ) :
    Measurable[fieldSigmaAlgebra 0 hC U] (fun ω => hC ω φ) := by
  have h : Measurable[fieldSigmaAlgebra 0 hC U] (fun ω => fieldPairing 0 (hC ω) φ) := by
    refine Measurable.of_comap_le ?_
    unfold fieldSigmaAlgebra
    exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ) =>
      MeasurableSpace.comap (fun ω => fieldPairing 0 (hC ω) ψ) inferInstance) φ hφ
  simpa [fieldPairing] using h

/-- An in-probability limit of pairings with tests supported in `U` has an a.s. equal version which is
`fieldSigmaAlgebra 0 hC U`-measurable. -/
theorem exists_fieldSigma_version_of_tendstoInMeasure {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (ψ : ℕ → ℂ → ℝ) (hψ : ∀ n, IsTestFunction U (ψ n)) (g : Ω → ℝ)
    (hconv : TendstoInMeasure P (fun n ω => hC ω (ψ n)) atTop g) :
    ∃ D : Ω → ℝ, Measurable[fieldSigmaAlgebra 0 hC U] D ∧ g =ᵐ[P] D := by
  obtain ⟨ns, -, hae⟩ := hconv.exists_seq_tendsto_ae
  refine ⟨fun ω => limsup (fun i => hC ω (ψ (ns i))) atTop, ?_, ?_⟩
  · let _ : MeasurableSpace Ω := fieldSigmaAlgebra 0 hC U
    exact Measurable.limsup (fun i => measurable_fieldPairing_zero_of_test hC U (ψ (ns i)) (hψ (ns i)))
  · filter_upwards [hae] with ω hω
    exact hω.limsup_eq.symm

/-- **Reduction of the cone locality Step.** The absolute approximation `hAbs` (for every cone field and every
closed disk `closedBall x ε ⊆ U`, the circle average `h_ε(x)` is an in-probability limit of pairings with tests in `U`)
gives `ConeCircleAverageLocalityStep`. `hAbs` is an explicit hypothesis here, not a proved fact. -/
theorem coneCircleAverageLocalityStep_of_absApprox
    (hAbs : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ U : Set ℂ, IsOpen U → ∀ (ε : ℝ) (x : ℂ), 0 < ε → closedBall x ε ⊆ U →
        ∃ ψ : ℕ → ℂ → ℝ, (∀ n, IsTestFunction U (ψ n)) ∧
          TendstoInMeasure P (fun n ω => hC ω (ψ n)) atTop (fun ω => hcirc ω ε x)) :
    ConeCircleAverageLocalityStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc hP hQ U hU ε x hε hsub
  obtain ⟨ψ, hψ, hconv⟩ := hAbs γ hγ0 hγ2 Ω P hC hcirc hP hQ U hU ε x hε hsub
  exact exists_fieldSigma_version_of_tendstoInMeasure hC U ψ hψ _ hconv

end MatedCRT
