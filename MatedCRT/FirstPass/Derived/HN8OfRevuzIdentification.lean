import MatedCRT.FirstPass.Derived.HN8OfReferenceGoodSet
import MatedCRT.FirstPass.Derived.LBMInvariantOfInvTC
import MatedCRT.FirstPass.Derived.RevuzInvariant
import MatedCRT.FirstPass.Derived.LBMPathLawFieldMarkov

/-!
# The law-a.e. Markov and invariance statement from the Revuz identification

For a valid environment, the clock `S.clock ω` of the Liouville Brownian motion has, almost surely, a version `G`
which is a positive continuous additive functional (PCAF) of planar Brownian motion with a good clock
(`MatedCRTEnv.IsValid.ae_exists_pcaf_goodClock_clock`). This file shows that the identification of the Revuz measure
of such a version with the Liouville quantum gravity measure,
`revuz planarLaw G = S.μ ω`, is the only remaining ingredient of the law-a.e. statement `hN8'`.

* `ae_isInvariantFor_lbmPathLawField_of_revuz_eq`: if almost surely some PCAF version `G` with a good clock has
  Revuz measure `S.μ ω`, then almost surely `S.μ ω` is invariant for the law field `lbmPathLawField γ (pairJ ⊤ (H ω))`
  of the rescaled Liouville Brownian motion. The Revuz measure is invariant for the time change (`isInvTC_revuz`),
  invariance transfers to the law field of the time-changed paths (`isInvariantFor_of_isInvTC`), and to the rescaled
  law field (`IsInvariantFor.lbmPathLawField`).
* `ae_markovTCBM_invariant_of_revuz_eq`: together with the quenched Markov property
  (`FirstPass.Derived.ae_isMarkovTCBM_lbmPathLawField`).
* `markovTCBM_invariant_law_of_revuz_identification` and
  `markovTCBM_invariant_law_of_forall_revuz_identification`: `hN8'`, exactly as typed, from the reference
  environments of the model and the Revuz identification for valid environments on `ℝ`
  (`markovTCBM_invariant_law_of_referenceEnvironments`).
-/

namespace MatedCRT

open MeasureTheory MarkovProcess
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure lbmLawContinuity_of_isValid)
open scoped NNReal ENNReal

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
  {H : Ω → LQGMetric.DistC}

/-- **Invariance of the LQG measure for the Liouville Brownian law field, from the Revuz identification.**  For a
valid environment at `0 < γ < 2` and a measurable version `H` of its field: if almost surely the clock `S.clock ω`
has a version `G` which is a positive continuous additive functional of planar Brownian motion with a good clock and
whose Revuz measure is the LQG measure `S.μ ω`, then almost surely `S.μ ω` is invariant for the law field
`lbmPathLawField γ (pairJ ⊤ (H ω))`. -/
theorem ae_isInvariantFor_lbmPathLawField_of_revuz_eq (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hH : Measurable H) (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrevuz : ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) ∧ revuz planarLaw G = S.μ ω) :
    ∀ᵐ ω ∂S.P, IsInvariantFor (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) (S.μ ω) := by
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS)
  filter_upwards [hrevuz, hΛ, hS.isLQGClock] with ω hGω hω hclock
  obtain ⟨G, hA, hG, hGc, hrev⟩ := hGω
  have hinv : IsInvTC planarLaw G (S.μ ω) := by
    rw [← hrev]
    exact isInvTC_revuz hA hG
  refine IsInvariantFor.lbmPathLawField ?_
  exact isInvariantFor_of_isInvTC (F := S.clock ω) (G := G) (Filter.Eventually.of_forall hω)
    (Filter.Eventually.of_forall fun z => (hclock z).2) (Filter.Eventually.of_forall hGc) hinv

/-- **The Liouville Brownian law field is a Markovian time-changed Brownian motion with invariant measure the LQG
measure, quenched, from the Revuz identification.** -/
theorem ae_markovTCBM_invariant_of_revuz_eq (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hH : Measurable H) (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrevuz : ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) ∧ revuz planarLaw G = S.μ ω) :
    ∀ᵐ ω ∂S.P, IsMarkovTCBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) ∧
      IsInvariantFor (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) (S.μ ω) :=
  (FirstPass.Derived.ae_isMarkovTCBM_lbmPathLawField hγ hγ2 hS hH hrep).and
    (ae_isInvariantFor_lbmPathLawField_of_revuz_eq hγ hγ2 hS hH hrep hrevuz)

/-- The existential form of the Revuz identification follows from the universal form over adapted PCAF versions
with a good clock, since such a version exists almost surely
(`MatedCRTEnv.IsValid.ae_exists_pcaf_goodClock_clock`). -/
theorem ae_exists_revuz_eq_of_forall (hS : S.IsValid 𝒮 γ)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrevuz : ∀ᵐ ω ∂S.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G → GoodClock planarLaw G →
      (∀ t, Measurable[pathFiltration t] (G t)) →
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) → revuz planarLaw G = S.μ ω) :
    ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) ∧ revuz planarLaw G = S.μ ω := by
  filter_upwards [hS.ae_exists_pcaf_goodClock_clock hrep, hrevuz] with ω hGω hω
  obtain ⟨G, hA, hG, hGa, hGc⟩ := hGω
  exact ⟨G, hA, hG, hGc, hω G hA hG hGa hGc⟩

end ValidEnvironment

/-- **`hN8'` from the Revuz identification.**  Given the reference environments of the model, the law-a.e.
statement `hN8'` of the counted wrappers holds, exactly as typed, as soon as every valid environment `S₀` on `ℝ`
satisfies: almost surely its clock has a PCAF version with a good clock whose Revuz measure is the LQG measure
`S₀.μ r`. -/
theorem markovTCBM_invariant_law_of_revuz_identification {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮)
    (hrevuz : ∀ γ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ᵐ r ∂S₀.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
        (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S₀.clock r b t) ∧ revuz planarLaw G = S₀.μ r) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) :=
  markovTCBM_invariant_law_of_referenceEnvironments h10 fun γ hγ0 hγ2 S₀ hS₀ _ hH₀ hrep₀ =>
    ae_markovTCBM_invariant_of_revuz_eq hγ0 hγ2 hS₀ hH₀ hrep₀ (hrevuz γ hγ0 hγ2 S₀ hS₀)

/-- **`hN8'` from the Revuz identification, universal form.**  As
`markovTCBM_invariant_law_of_revuz_identification`, with the identification asked for every adapted PCAF version
with a good clock of the clock of a valid environment on `ℝ` with a measurable field version. -/
theorem markovTCBM_invariant_law_of_forall_revuz_identification {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮)
    (hrevuz : ∀ γ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ r ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC r φ = H₀ r φ) →
      ∀ᵐ r ∂S₀.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G → GoodClock planarLaw G →
        (∀ t, Measurable[pathFiltration t] (G t)) →
        (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S₀.clock r b t) → revuz planarLaw G = S₀.μ r) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) :=
  markovTCBM_invariant_law_of_referenceEnvironments h10 fun γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep₀ =>
    ae_markovTCBM_invariant_of_revuz_eq hγ0 hγ2 hS₀ hH₀ hrep₀
      (ae_exists_revuz_eq_of_forall hS₀ hrep₀ (hrevuz γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep₀))

end MatedCRT
