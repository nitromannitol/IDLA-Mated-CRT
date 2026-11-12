import MatedCRT.FirstPass.Derived.ConeAreaMeasureCode
import MatedCRT.FirstPass.Derived.ConeAreaNonatomic
import LatticeProb.LQG.MassReparamBorel
import LatticeProb.Prob.FiniteOnCompactsPart
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The area-parametrized curve as a Borel function of the field and the Lebesgue-parametrized curve

The last assertion of the area-scaling lemma (`lem:area-scale`, notes/env-steps/env-steps.tex:748-765): the curve
`η`, parametrized by the LQG area of the quantum cone, is almost surely a fixed Borel function of the pairings of the
field with test functions and of the whole-plane space-filling SLE `ηL` of the mating-of-trees coupling (any
parametrization of `ηL` that differs from `η` by an increasing homeomorphism of `ℝ` fixing `0`).

The decoder is explicit: the area measure is recovered from the field pairings by the universal Borel decoder
`coneAreaCode γ` (`exists_measurable_fieldCode_lqgMeasure`), replaced by its finite-on-compacts part (which changes
nothing almost surely, as the area measure is locally finite), and `ηL` is reparametrized by that measure
(`LatticeProb.LQG.massReparam`, the inverse of the signed mass clock).

* `MatedCRT.coneAreaCode`, `MatedCRT.measurable_coneAreaCode`,
  `MatedCRT.MatedCRTEnv.IsValid.ae_coneAreaCode_eq`: the decoder of the area measure as a definition.
* `MatedCRT.curveOfCode`, `MatedCRT.measurable_curveOfCode`: the reparametrization of a curve by a decoded measure,
  measurable at every time.
* `MatedCRT.curveOfCode_eq_of_isAreaParametrized`: pathwise, it returns the area-parametrized curve.
* `MatedCRT.MatedCRTEnv.IsValid.ae_coneCurveCode_eq`: almost surely, `η = coneCurveCode γ (h, ηL)`.
* `MatedCRT.MatedCRTEnv.IsValid.ae_coneCurveCode_eq_of_matingOfTrees`: the same for the curve `ηL` of any
  mating-of-trees coupling tied to the environment.
-/

open MeasureTheory Set
open HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- The universal Borel decoder of the area measure of the quantum cone from the pairings of the field with test
functions (a choice of the decoder of `exists_measurable_fieldCode_lqgMeasure`). -/
noncomputable def coneAreaCode (γ : ℝ) : FieldPairingCode → Measure ℂ :=
  (exists_measurable_fieldCode_lqgMeasure γ).choose

theorem measurable_coneAreaCode (γ : ℝ) : Measurable (coneAreaCode γ) :=
  (exists_measurable_fieldCode_lqgMeasure γ).choose_spec.1

/-- Almost surely, the decoder applied to the field pairings of a valid environment returns its area measure. -/
theorem MatedCRTEnv.IsValid.ae_coneAreaCode_eq {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, coneAreaCode γ (fieldPairingCode S ω) = S.μ ω :=
  (exists_measurable_fieldCode_lqgMeasure γ).choose_spec.2 hS

/-- The reparametrization of the curve `p.2` by the mass of the finite-on-compacts part of the measure decoded
from `p.1`. -/
noncomputable def curveOfCode (M : FieldPairingCode → Measure ℂ) (p : FieldPairingCode × C(ℝ, ℂ)) (t : ℝ) : ℂ :=
  LatticeProb.LQG.massReparam (LatticeProb.finiteOnCompactsPart (M p.1)) p.2 t

/-- The reparametrized curve is measurable in the code at every time, for a measurable decoder. -/
theorem measurable_curveOfCode {M : FieldPairingCode → Measure ℂ} (hM : Measurable M) (t : ℝ) :
    Measurable fun p : FieldPairingCode × C(ℝ, ℂ) => curveOfCode M p t :=
  LatticeProb.LQG.measurable_massReparam
    (LatticeProb.measurable_finiteOnCompactsPart_comp (hM.comp measurable_fst))
    (fun _ => inferInstance) (fun p => p.2.continuous)
    (fun s => (continuous_eval_const s).measurable.comp measurable_snd) t

/-- **Pathwise recovery.** If the decoder returns a measure `μ` finite on compact sets along which `η` is
parametrized by area, and `η = L ∘ φ` for an increasing homeomorphism `φ` of `ℝ` fixing `0`, then the
reparametrization of `L` by the decoded measure is `η`. -/
theorem curveOfCode_eq_of_isAreaParametrized {M : FieldPairingCode → Measure ℂ} {c : FieldPairingCode}
    {L : C(ℝ, ℂ)} {μ : Measure ℂ} {η : ℝ → ℂ} (hc : M c = μ) [IsFiniteMeasureOnCompacts μ]
    (hη : IsAreaParametrized μ η) (hφ : ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η t = L (φ t)) (t : ℝ) :
    curveOfCode M (c, L) t = η t := by
  obtain ⟨φ, hφ0, hφt⟩ := hφ
  have harea : ∀ s u : ℝ, s ≤ u → μ (η '' Icc s u) = ENNReal.ofReal (u - s) := by
    intro s u hsu
    rcases hsu.lt_or_eq with h | rfl
    · exact hη.2.2.2 s u h
    · rw [Icc_self, image_singleton, hη.measure_singleton_eq_zero, sub_self, ENNReal.ofReal_zero]
  unfold curveOfCode
  rw [hc, LatticeProb.finiteOnCompactsPart_eq_self]
  exact LatticeProb.LQG.massReparam_eq_of_massParam μ L η φ hφ0 hφt harea t

/-- The decoder of the area-parametrized curve from the field pairings and the Lebesgue-parametrized curve. -/
noncomputable def coneCurveCode (γ : ℝ) : FieldPairingCode × C(ℝ, ℂ) → ℝ → ℂ :=
  curveOfCode (coneAreaCode γ)

theorem measurable_coneCurveCode (γ : ℝ) (t : ℝ) :
    Measurable fun p : FieldPairingCode × C(ℝ, ℂ) => coneCurveCode γ p t :=
  measurable_curveOfCode (measurable_coneAreaCode γ) t

/-- **The area-parametrized curve is a Borel function of the field and the Lebesgue-parametrized curve**
(env-steps.tex:748-765). For a valid environment and any random continuous curve `ηL` with `η = ηL ∘ φ` almost
surely, for an increasing homeomorphism `φ` of `ℝ` fixing `0`, almost surely `η = coneCurveCode γ (h, ηL)`. -/
theorem MatedCRTEnv.IsValid.ae_coneCurveCode_eq {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ηL : Ω → C(ℝ, ℂ))
    (hφ : ∀ᵐ ω ∂S.P, ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, S.η ω t = ηL ω (φ t)) :
    ∀ᵐ ω ∂S.P, ∀ t, coneCurveCode γ (fieldPairingCode S ω, ηL ω) t = S.η ω t := by
  filter_upwards [hS.ae_coneAreaCode_eq, hS.isLQGMeasure, hS.isAreaParametrized, hφ] with ω hc hL hη hω t
  have := hL.isLocallyFiniteMeasure
  exact curveOfCode_eq_of_isAreaParametrized hc hη hω t

/-- The same for the whole-plane space-filling SLE `ηL` of any mating-of-trees coupling tied to the
environment (the form of `MatedCRTEnv.IsValid.matingOfTrees`). -/
theorem MatedCRTEnv.IsValid.ae_coneCurveCode_eq_of_matingOfTrees {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm)
    (htie : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ∀ t, coneCurveCode γ (fieldPairingCode S ω, ηL ω) t = S.η ω t := by
  refine hS.ae_coneCurveCode_eq ηL ?_
  filter_upwards [hC.areaParam, htie] with ω hap hω
  obtain ⟨⟨φ, hφ0, hφ⟩, -⟩ := hap
  exact ⟨φ, hφ0, fun t => by rw [← hω]; exact hφ t⟩

end MatedCRT
