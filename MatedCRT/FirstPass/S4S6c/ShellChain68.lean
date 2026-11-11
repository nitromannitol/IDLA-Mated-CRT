import MatedCRT.FirstPass.S6r.WindowEventMeasurable
import MatedCRT.Proofs.Measurability.LQGMeasureField

/-!
# The field-measurable short window family

`ShellChainStmt` (S4S6c/Guard68S10.lean:70) needs a window family `Ew` with `MeasurableSet[S.fieldSigma] (Ew δ)` and
polynomially high probability. The window event of `S.μ` is the bad event
`badWindowOf S.μ ρ a c₀ C δ` of `ShortWindowGoodRadiusPrevalenceStmt` (S6r/ShortWindow.lean:61); its complement is the
good window. `S.μ` is only almost surely `S.fieldSigma`-measurable (`LQGMeasureFieldMeasurableStep`, GoodScale.lean:316,
proved as `lqgMeasureFieldMeasurableStep`, Proofs/Measurability/LQGMeasureField.lean:75). Let `μ'` be that version.

* `badWindowOf μ' ...` is `S.fieldSigma`-measurable (`measurableSet_shortWindowEvent_of_measurable`,
  S6r/WindowEventMeasurable.lean), so `Ew δ := (badWindowOf μ' ... δ)ᶜ` is `S.fieldSigma`-measurable.
* `S.P (badWindowOf μ' δ) ≤ S.P (badWindowOf S.μ δ)`, because the two bad events differ only inside the null set
  `{μ' ≠ S.μ}`. The bound `ofReal (C' * δ^6)` of the prevalence statement then gives `PolyHighProb`.
* Almost surely, `ω ∈ Ew δ → ω ∉ badWindowOf S.μ δ`.

The pointwise form (for every `ω`, not almost every) is NOT obtained here: the exceptional null set
`{μ' ≠ S.μ}` is not known to be `S.fieldSigma`-measurable. That is the gap reported for `ShellChainStmt`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68ShellChain

open MatedCRT.Lemma68Window

/-- The bad window event at scale `d` for the measure field `μ`: some eligible centre has no good seven-adic radius in
`[d, d^a]` (the event of `ShortWindowGoodRadiusPrevalenceStmt`, S6r/ShortWindow.lean:61). -/
def badWindowOf {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) : Set Ω :=
  {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a, ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z}

/-- The bad window events of two measure fields agree at every `ω` where the fields agree. -/
theorem badWindowOf_iff_of_eq {Ω : Type} (μ μ' : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (h : μ' ω = μ ω) : ω ∈ badWindowOf μ' ρ a c₀ C d ↔ ω ∈ badWindowOf μ ρ a c₀ C d := by
  simp only [badWindowOf, Set.mem_ofPred_eq, h]

/-- **The field-measurable short-window family, almost-sure form.** For a valid environment `S` with the window prevalence
bound `hprev : ShortWindowGoodRadiusPrevalenceStmt` (the named input of `shortWindow_prevalence`, S6r/ShortWindow.lean:297),
there are a constant `C` and a family `Ew` of good windows such that `Ew δ` is `S.fieldSigma`-measurable, `Ew` has
polynomially high probability, and for each `δ` almost every `ω ∈ Ew δ` avoids the bad window of `S.μ`. -/
theorem shortWindow_fieldFamily_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (hprev : ShortWindowGoodRadiusPrevalenceStmt) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (c₀ : ℝ) (hc0 : 0 < c₀) (hc1 : c₀ < 1 / 5) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
      HarmonicBalls.PolyHighProb S.P Ew ∧
      ∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ a c₀ C δ := by
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev a ha0 ha1 γ hγ hγ2 c₀ hc0 hc1
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  obtain ⟨μ', hμ'm, hμ'ae⟩ := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮 γ hγ hγ2 Ω S hS
  have hN : S.P {ω | ¬ (μ' ω = S.μ ω)} = 0 := ae_iff.1 hμ'ae
  have hbad_le : ∀ δ : ℝ, S.P (badWindowOf μ' ρ a c₀ C δ) ≤ S.P (badWindowOf S.μ ρ a c₀ C δ) := by
    intro δ
    calc S.P (badWindowOf μ' ρ a c₀ C δ)
        ≤ S.P (badWindowOf S.μ ρ a c₀ C δ ∪ {ω | ¬ (μ' ω = S.μ ω)}) := by
          refine measure_mono (fun ω hω => ?_)
          by_cases h : μ' ω = S.μ ω
          · exact Or.inl ((badWindowOf_iff_of_eq S.μ μ' ρ a c₀ C δ ω h).1 hω)
          · exact Or.inr h
      _ ≤ S.P (badWindowOf S.μ ρ a c₀ C δ) + S.P {ω | ¬ (μ' ω = S.μ ω)} := measure_union_le _ _
      _ = S.P (badWindowOf S.μ ρ a c₀ C δ) := by rw [hN, add_zero]
  refine ⟨C, fun δ => (badWindowOf μ' ρ a c₀ C δ)ᶜ, ?_, ?_, ?_⟩
  · intro δ
    exact (WindowEventMeasurable.measurableSet_shortWindowEvent_of_measurable μ' hμ'm ρ δ a c₀ C).compl
  · refine ⟨6, by norm_num, C', 1, one_pos, fun r hr hr1 => ?_⟩
    rw [compl_compl, show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    exact (hbad_le r).trans (hP ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hcone r hr hr1)
  · intro δ
    filter_upwards [hμ'ae] with ω hω hin hbad
    exact hin ((badWindowOf_iff_of_eq S.μ μ' ρ a c₀ C δ ω hω).2 hbad)

end Lemma68ShellChain
end MatedCRT
