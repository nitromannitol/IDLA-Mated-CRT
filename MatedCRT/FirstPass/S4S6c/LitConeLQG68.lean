import MatedCRT.FirstPass.S2VG.Literature
import MatedCRT.Defs.QuantumCone

/-!
# The named literature input for the quantum-cone LQG measure

`LitQuantumConeLQGMeasureExistence` is the inline binder `hμ` of the closed Section 6 theorems
(`closed_6_x_hU`, `closed_6_7/8/9_hU_eps`, Closed6x68.lean): for every `γ ∈ (0,2)`, on every probability space carrying a
quantum cone field `hcone`/`hcirc` (Duplantier-Sheffield), there is an LQG measure `μ` of that field.

Source (Q4): the canonical quantum-cone field
of Duplantier-Sheffield (arXiv:1409.7055, Definition 4.10 and the description of the circle-average embedding) together
with the subcritical GMC construction of its LQG measure. It is a literature input, not a result of the IDLA paper.

PENDING TRUTH CHECK: the Prop is not yet in `MatedCRT/External` and its exact form is not yet audited against the
Duplantier-Sheffield statement; it is defined here, as a named binder only, until it is promoted or retired.
-/

namespace MatedCRT.S2VG

open MeasureTheory HarmonicBalls

/-- **Literature input (class b), quantum-cone LQG measure existence.** For `γ ∈ (0,2)`, every probability space `P`
carrying a quantum cone field `(hcone, hcirc)` admits an LQG measure `μ` of that field (`IsLQGMeasure P γ hcirc μ`).
Duplantier-Sheffield, arXiv:1409.7055 (Def. 4.10; subcritical GMC). PENDING TRUTH CHECK. -/
abbrev LitQuantumConeLQGMeasureExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
    ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ

end MatedCRT.S2VG
