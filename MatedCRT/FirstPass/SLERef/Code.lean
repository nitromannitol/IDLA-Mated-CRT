import MatedCRT.Defs.Setting

/-!
# First pass: the normalized law of whole-plane space-filling SLE (task fp-SLERef-reference-law, worker z10)

`SLEPathCode`, `slePathCode` and `IsLebesgueRepresentative` are promoted unchanged from the probe
`notes/z2-sle-field-probe.lean` (namespace `MatedCRT.Probe`, z2, 2026-11-10 01:35 UTC). The new declaration
`HasNormalizedSLELaw 𝒮 ν` replaces the probe's stand-in `canonicalSLECodeLaw` by an explicit law family `ν`.
Design: `notes/fp-gaps/CHATGPT-z2-sle-field-design.md` §1, §7, §8.

Nothing in this module asserts that a family `ν` is the law of an SLE, nor that a measurable normalized representative
exists. The reference existence and the uniform literature transfer are the frozen input `SLEReferenceExistsInput`
(`MatedCRT/FirstPass/Frozen/SLERef.lean`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The rational-time code of a path: the point `(c q)_{q ∈ ℚ}` of `ℚ → ℂ`, with the product σ-algebra. -/
abbrev SLEPathCode := ℚ → ℂ

/-- The rational-time code `q ↦ c q` of a continuous path `c : ℝ → ℂ`. -/
def slePathCode (c : C(ℝ, ℂ)) : SLEPathCode :=
  fun q => c (q : ℝ)

/-- `c` is a Lebesgue-area parametrized representative of the curve `η` (modulo increasing reparametrization):
`c 0 = 0`, `c` is onto `ℂ` and proper, `volume (c '' [s, t]) = t - s` for `s ≤ t`, and `η = c ∘ φ` for an order
isomorphism `φ` of `ℝ` with `φ 0 = 0`. -/
def IsLebesgueRepresentative
    (η : ℝ → ℂ) (c : C(ℝ, ℂ)) : Prop :=
  c 0 = 0 ∧
  Function.Surjective c ∧
  Tendsto c (cocompact ℝ) (cocompact ℂ) ∧
  (∀ s t : ℝ, s ≤ t →
    volume (c '' Set.Icc s t) =
      ENNReal.ofReal (t - s)) ∧
  ∃ φ : ℝ ≃o ℝ,
    φ 0 = 0 ∧
    ∀ t : ℝ, η t = c (φ t)

/-- **Normalized law of whole-plane space-filling SLE** (a definition, not an input). For a space-filling SLE model
`𝒮` and a family `ν : ℝ → Measure SLEPathCode`, `HasNormalizedSLELaw 𝒮 ν` says: whenever `P` is a probability measure
on an ambient measurable space `mΩ`, `𝓕` is a sigma algebra, `κ > 4`, `𝒮.IsSLE P 𝓕 κ η` holds, and `ηL` is an
`mΩ`-measurable family of continuous paths which is almost surely a Lebesgue-area representative of `η`, then the law
of the rational-time code of `ηL` is `ν κ`.

Limitations, recorded for the consumers: (1) the law is identified only when a measurable representative `ηL` is
given; no existence of such a representative is asserted here (for valid environments it comes from the coupling);
(2) it identifies a marginal law only; independence from `𝓕` is not part of this proposition. The sigma algebra `𝓕`
is never required to make `ηL` measurable; the measurability is with respect to the ambient `mΩ` (design §7). -/
def HasNormalizedSLELaw (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω)
    (P : @Measure Ω mΩ)
    (𝓕 : MeasurableSpace Ω)
    (κ : ℝ)
    (η : Ω → ℝ → ℂ)
    (ηL : Ω → C(ℝ, ℂ)),
    IsProbabilityMeasure P →
    4 < κ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η →
    Measurable[mΩ] ηL →
    (∀ᵐ ω ∂P,
      IsLebesgueRepresentative (η ω) (ηL ω)) →
    @Measure.map Ω SLEPathCode mΩ _
      (fun ω => slePathCode (ηL ω)) P = ν κ

end MatedCRT
