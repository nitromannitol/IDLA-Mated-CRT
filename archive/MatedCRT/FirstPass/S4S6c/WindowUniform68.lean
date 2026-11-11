import MatedCRT.FirstPass.S4S6c.ShellChainCore68

/-!
# Uniform window avoidance and simultaneous window membership

Three results, each obtained from landed lemmas (no new mathematics):

* `badWindow_avoid_uniform`: from the single almost-sure identity `μ' = μ` (independent of the scale), almost surely,
  for every scale `δ` at once, `ω ∈ (badWindowOf μ' δ)ᶜ` implies `ω ∉ badWindowOf μ δ` (part 1).
  `badWindowOf` is ShellChain68.lean:33, `badWindowOf_iff_of_eq` is ShellChain68.lean:37.
* `shortWindow_fieldFamily_uniform`: `shortWindow_fieldFamily_at` (ShellChainCore68.lean:42) with the avoidance conjunct
  in the uniform form `∀ᵐ ω, ∀ δ, ...` instead of `∀ δ, ∀ᵐ ω, ...`. The proof is that of `shortWindow_fieldFamily_at`
  with the last step replaced by `badWindow_avoid_uniform`.
* `shortWindow_fieldFamily_cutoff`: the same family together with the dyadic cutoff `dd` of `window_cutoff`
  (Guard68S10.lean:114): almost surely `ω ∈ Ew (dyadicD r)` for every `0 < r ≤ dd ω`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, prevalence of good radii), Duplantier-Sheffield (LQG measure).
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68WindowUniform

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ChainCore DyadicCutoff68 Lemma68Window

/-- **Uniform avoidance from one almost-sure field identity (part 1).** If `μ'` agrees with `μ` almost
surely, then almost surely, for every scale `δ` simultaneously, a point of the complement of the bad window of `μ'`
is outside the bad window of `μ`. The exceptional null set `{μ' ≠ μ}` does not depend on `δ`. -/
theorem badWindow_avoid_uniform {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ μ' : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, μ' ω = μ ω) (ρ a c₀ C : ℝ) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, ω ∈ (badWindowOf μ' ρ a c₀ C δ)ᶜ → ω ∉ badWindowOf μ ρ a c₀ C δ := by
  filter_upwards [hμ] with ω hω δ hin hbad
  exact hin ((badWindowOf_iff_of_eq μ μ' ρ a c₀ C δ ω hω).2 hbad)

/-- **The field-measurable short-window family, uniform avoidance.** This is `shortWindow_fieldFamily_at`
(ShellChainCore68.lean:42) with the avoidance conjunct in the uniform form: almost surely, `ω ∈ Ew δ` implies
`ω ∉ badWindowOf S.μ δ` for every `δ` at once. -/
theorem shortWindow_fieldFamily_uniform {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (a c₀ C C' ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hP : WindowPrevAt γ a c₀ C C') :
    ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
      HarmonicBalls.PolyHighProb S.P Ew ∧
      ∀ᵐ ω ∂S.P, ∀ δ : ℝ, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ a c₀ C δ := by
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
  refine ⟨fun δ => (badWindowOf μ' ρ a c₀ C δ)ᶜ, ?_, ?_, ?_⟩
  · intro δ
    exact (WindowEventMeasurable.measurableSet_shortWindowEvent_of_measurable μ' hμ'm ρ δ a c₀ C).compl
  · refine ⟨6, by norm_num, C', 1, one_pos, fun r hr hr1 => ?_⟩
    rw [compl_compl, show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    exact (hbad_le r).trans (hP ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hcone r hr hr1)
  · exact badWindow_avoid_uniform S.P S.μ μ' hμ'ae ρ a c₀ C

/-- **Field-measurable window family with simultaneous membership (part 2).** The family of
`shortWindow_fieldFamily_uniform` carries the cutoff `dd` of `window_cutoff` (Guard68S10.lean:114): `dd` is
field-measurable with values in `(0, 1]`, and almost surely every dyadic window event `ω ∈ Ew (dyadicD r)` holds
for all `0 < r ≤ dd ω` at once. Nothing is claimed for `r > dd ω`. -/
theorem shortWindow_fieldFamily_cutoff {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (a c₀ C C' ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hP : WindowPrevAt γ a c₀ C C') :
    ∃ (Ew : ℝ → Set Ω) (dd : Ω → ℝ), (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
      HarmonicBalls.PolyHighProb S.P Ew ∧
      (∀ᵐ ω ∂S.P, ∀ δ : ℝ, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ a c₀ C δ) ∧
      Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ 1) ∧
      ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → r ≤ dd ω → ω ∈ Ew (dyadicD r) := by
  obtain ⟨Ew, hEwm, hEwp, hav⟩ := shortWindow_fieldFamily_uniform hγ hγ2 S hS a c₀ C C' ρ hρ hρ1 hP
  obtain ⟨dd, hdm, hdpos, hdle, hmem⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  exact ⟨Ew, dd, hEwm, hEwp, hav, hdm, hdpos, hdle, hmem⟩

end Lemma68WindowUniform
end MatedCRT
