import Mathlib
import MatedCRT.Defs.Setting

/-!
# FIRST PASS: the measurable-environment hypothesis of LEMMA68

`MatedCRTEnv`
(`Defs/Setting.lean:105`) and `MatedCRTEnv.IsValid` (`Defs/Setting.lean:141`) carry no measurability of the
curve `η` at rational times, of the transition weights, or of the escape of `η` from `∞`. The measurable
realization of the SLE/LQG environment (Bou-Rabee-Gwynne §1.1.4, §2.4; Miller-Sheffield IG IV) supplies these facts.
They are collected in ONE named structure, taken as an explicit hypothesis by the B1/B2 statements, and are
NOT a validity field of `IsValid`: an implication from `IsValid 𝒮 γ` for an unconstrained `𝒮` would be unjustified,
since `IsSLE` is an arbitrary predicate.
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Inputs

/-- The curve `η : ℝ → ℂ` escapes both ends: for every `R > 0` there is `T > 0` with `‖η t‖ > R` whenever
`|t| ≥ T` (the two ends of the whole-plane curve, Bou-Rabee-Gwynne §1.1.4). -/
def CurveEscapesBothEnds (η : ℝ → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ |t| → R < ‖η t‖

/-- The measurable-environment inputs of LEMMA68 (write-up §1.2), with `p ω u v` the quenched transition weights of
the walk at the mesh `ε`:
* `eta_rat_measurable`: `ω ↦ η ω q` is measurable at every rational time `q` (evaluations at deterministic times);
* `transition_measurable`: each transition weight `ω ↦ p ω u v` is measurable;
* `eta_escapes`: almost surely `η ω` escapes both ends.
This is ONE named hypothesis (a structure of Prop fields) for the B1 and B2 statements; it is not frozen. -/
structure Lemma68MeasurableInputs {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (p : Ω → ℤ → ℤ → ℝ≥0∞) : Prop where
  eta_rat_measurable : ∀ q : ℚ, Measurable (fun ω => S.η ω (q : ℝ))
  transition_measurable : ∀ u v : ℤ, Measurable (fun ω => p ω u v)
  eta_escapes : ∀ᵐ ω ∂S.P, CurveEscapesBothEnds (S.η ω)

/-- (OPEN 4 of the round-6 notes) A valid environment gives the almost-sure continuity of the curve `η`: this is the
first clause of `IsAreaParametrized` (`Defs/Setting.lean:126`), carried by the field `isAreaParametrized`
(`Defs/Setting.lean:152`). The continuity hypothesis of `ae_cellDist_eq_iInf_cell` is therefore available for every
valid environment. -/
theorem ae_continuous_of_isValid {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (h : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, Continuous (S.η ω) :=
  h.isAreaParametrized.mono fun _ hω => hω.1

end Lemma68Inputs

end MatedCRT
