import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1

/-!
# The step from the zero-cone field to the curve in the ergodicity of the shifted zero-cone configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1)
infer from the independence of the jointly invariant functional `G'(h, η̂)` from `h` that `G'` is almost surely a
function of `η̂` alone (`ZeroConeCurveFactorStep`). The written argument shows that the independence-to-factor inference is not valid in general,
and proves instead (by a local approximation at a uniform root) that every bounded functional of
`(h, e)` which is invariant under the simultaneous coordinate change is almost surely constant: "This proves G1 with
`g(e)` a constant".

This file states that conclusion as the named hypothesis `ZeroConeJointLemmaA1` (Lemma A.1 of arXiv:1705.11161 for
the zero-cone field jointly with the independent space-filling SLE) and derives `ZeroConeCurveFactorStep` from it
with a constant `g` (`zeroConeCurveFactorStep`); the independence premise of the step is not used.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161) for the zero-cone field jointly with the space-filling
SLE** (the written argument: "Let `V(h, e)` be bounded and invariant in the
simultaneous sense in G1 ... Since `V` is also independent of `𝒟`, it is constant. This proves G1 with `g(e)` a
constant"; the argument there uses Lemma A.4 of arXiv:1705.11161 (law of the field at a uniform root, lines 19-23),
the growth `r(z)/|z| → 0` of the unit-mass radius (line 25; Rhodes–Vargas, arXiv:1305.6221, Theorem 2.12, and
§2.3.1 and Lemma A.3 of arXiv:1705.11161), the triviality of the joint exterior tail of the zero-cone field and the
imaginary-geometry field (line 27) and the exterior-measurable local approximations at uniform roots (lines 29-33)).
PENDING TRUTH CHECK.

Every bounded measurable functional `G'` of (field, curve) which, for almost every `h` (law of the zero-cone field)
and almost every `e` (law of `ηL`), satisfies `G'(h(C · + z) + Q log C, ψ⁻¹ ∘ e re-rooted at z) = G'(h, e)` for all
`C > 0` and `z ∈ ℂ` (`ψ(w) = C w + z`), is almost surely constant along `(h₀, ηL)`. -/
def ZeroConeJointLemmaA1 (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G' : Field × C(ℝ, ℂ) → ℝ, Measurable G' → (∃ M : ℝ, ∀ x, |G' x| ≤ M) →
    (∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      G' (lqgSimilarityField γ C z h, affineReroot z C 0 e) = G' (h, e)) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, G' (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) = c

/-- **The step from `h` to `η̂`** (arXiv:1705.11161; the written argument) from the joint form of Lemma A.1: the jointly invariant functional
`G'` is almost surely a constant `c`, so `g = c` is a measurable function of the curve, invariant under every
coordinate change. -/
theorem zeroConeCurveFactorStep (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hJ : ZeroConeJointLemmaA1 D hγ) : ZeroConeCurveFactorStep D hγ := by
  intro G' hG'm hbd hinv _
  obtain ⟨c, hc⟩ := hJ G' hG'm hbd hinv
  exact ⟨fun _ => c, measurable_const, hc, fun _ _ _ => Eventually.of_forall fun _ => rfl⟩

end Hypotheses

end MatedCRT
