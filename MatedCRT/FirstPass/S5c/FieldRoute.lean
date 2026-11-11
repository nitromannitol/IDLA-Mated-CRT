import MatedCRT.FirstPass.S5c.B1bThreshold
import MatedCRT.FirstPass.S5c.TestIntegralAE

/-!
# FIRST PASS, Lemma 5.3 (B1b): the least supersolution is AE-measurable on the field route

Steps: (1) the field σ-algebra `fieldSigmaAlgebra 0 hC univ` (the σ-algebra of the field,
HarmonicBalls.Defs.GFF) is contained in the ambient σ-algebra when the pairings `ω ↦ hC ω φ` are measurable (the content of
`IsQuantumCone.measurable_pairing`, Defs/QuantumCone.lean:84); (2) a field-measurable version `g` of `μ` gives the AE-form test
integrals (TestIntegralAE.lean); (3) B1b (B1bThreshold.lean) then makes `ω ↦ leastSupersolution (μ ω) R 0 u p` AE-measurable.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal

/-- **Field σ-algebra inside the ambient one**: if the pairings `ω ↦ hC ω φ` are measurable for test functions, the field
σ-algebra `fieldSigmaAlgebra 0 hC univ` is contained in the ambient σ-algebra (the pairing is `hC φ - 0 · ∫ φ log|·|`). -/
theorem fieldSigma_le_of_pairing_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (hC : Ω → (ℂ → ℝ) → ℝ)
    (hmeas : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ) :
    fieldSigmaAlgebra 0 hC Set.univ ≤ mΩ := by
  unfold fieldSigmaAlgebra
  refine iSup₂_le fun φ hφ => ?_
  have h : Measurable fun ω => fieldPairing 0 (hC ω) φ := by
    simpa [fieldPairing] using hmeas φ hφ
  exact h.comap_le

/-- **B1b on the field route** (operator rulings 20:12 and 20:16 UTC): for a random measure `μ_ω` with a field-measurable version
`g` (`μ = g` a.s., measurable for the field σ-algebra `m ≤ mΩ`), finite mass on the disc and bounded-below supersolution values at
`p ∈ B̄_R`, the least supersolution value `ω ↦ v(u)(p)(μ_ω)` is AE-measurable. The Lusin input and the test-function family are as in
B1bThreshold.lean. -/
theorem aemeasurable_leastSupersolution_of_fieldMeasurable {Ω : Type} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ g : Ω → Measure ℂ} (hg : Measurable[m] g)
    (hμg : ∀ᵐ ω ∂P, μ ω = g ω) {R u : ℝ} (hR : 0 ≤ R) (hu : 0 < u)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions (μ ω) R 0 u)) :
    AEMeasurable (fun ω => leastSupersolution (μ ω) R 0 u p) P :=
  aemeasurable_leastSupersolution_of_moments hF1 hR hu hμ
    (fun _ hφ hsupp => aemeasurable_integral_of_measurable_version hm hg hμg hμ hφ hsupp)
    φs hφs hdense hG hp hbdd

end MatedCRT.S5c
