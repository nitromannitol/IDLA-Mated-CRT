import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBFinal

/-!
# Lemma 3.11 at every real mesh for a valid environment on a standard Borel space

Gwynne–Miller–Sheffield, Lemma 3.11 (3.35), graph disconnection by the simple random walk on the mated-CRT map, holds at
every real cell size `ε ∈ (0, 1)` for the embedded mated-CRT map of every mating-of-trees coupling on a standard Borel
space (`MatedCRTHarmonic.GMSMain.EpsB.lemma311Real_of_coupling`). A valid environment `S` carries such a coupling
(the `matingOfTrees` clause of `MatedCRTEnv.IsValid`): its boundary-length pair is `S.bm` and its curve `η'` is a
measurable version of `S.η`. This file transfers the estimate to valid environments.

## Main results

* `lemma311Real_of_isValid`: for a valid environment `S` with parameter `γ ∈ (0, 2)` on a standard Borel space and every
  `ρ ∈ (0, 1)`, there are a measurable curve `η'` with `η' = S.η` almost surely and constants `α, β, p > 0`, `C` such
  that, for every `ε ∈ (0, 1)`, the event `Lemma311GoodReal S.bm η' ε ρ β p` of (3.35) at mesh `ε` fails with
  probability at most `C ε^α`;
* `exists_reference_lemma311Real`: the same for a valid reference environment on `ℝ`, given that `𝒮` has valid
  environments on `ℝ` for every `γ ∈ (0, 2)` (the body of `MatedCRT.HasReferenceEnvironments`,
  `MatedCRT/FirstPass/SLERef/Reference.lean`; a proof of that proposition is accepted as the hypothesis by
  unfolding).
-/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- **Lemma 3.11 at every real mesh for a valid environment.** Let `S` be a valid environment with parameter
`γ ∈ (0, 2)` on a standard Borel space and `ρ ∈ (0, 1)`. Then the curve `η'` of the mating-of-trees coupling of `S` is
measurable and almost surely equal to `S.η`, the boundary-length pair `S.bm` is measurable, and there are
`α, β, p > 0` and `C` such that for every `ε ∈ (0, 1)`, outside an event of probability at most `C ε^α`, the mesh-`ε`
mated-CRT map of `S.bm` is locally finite, its cells `η'([ε(x - 1), ε x])` form a cellular embedding, and (3.35) holds:
for every `z` and `r ∈ [ε^β, ρ]` with `B_{2r}(z) ⊂ B_ρ(0)`, the walk started in `B_r(z)` disconnects `∂B_{r/2}(z)`
from `∂B_{2r}(z)` in the graph before hitting `∂B_{2r}(z)` with quenched probability at least `p`. -/
theorem lemma311Real_of_isValid {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ η' : Ω → C(ℝ, ℂ), Measurable η' ∧ Measurable S.bm ∧ (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) ∧
      ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          S.P (MatedCRTHarmonic.GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ρ β p)ᶜ ≤
            ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  exact ⟨η', hMoT.measurable_curves.2.1, hMoT.measurable_curves.2.2.2, hae.mono fun ω h => h.1,
    MatedCRTHarmonic.GMSMain.EpsB.lemma311Real_of_coupling hMoT inferInstance ⟨hγ0, hγ2⟩ hρ0 hρ1⟩

/-- **Lemma 3.11 at every real mesh for a reference environment.** If the model `𝒮` has valid reference environments
on `ℝ` (the hypothesis is the body of `HasReferenceEnvironments 𝒮`), then for every `γ ∈ (0, 2)` and `ρ ∈ (0, 1)` there
is a valid environment `S` on `ℝ` with parameter `γ` for which the conclusion of `lemma311Real_of_isValid` holds. -/
theorem exists_reference_lemma311Real {𝒮 : SpaceFillingSLEModel}
    (h𝒮 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ S : MatedCRTEnv ℝ, S.IsValid 𝒮 γ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ S : MatedCRTEnv ℝ, S.IsValid 𝒮 γ ∧
      ∃ η' : ℝ → C(ℝ, ℂ), Measurable η' ∧ Measurable S.bm ∧ (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) ∧
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            S.P (MatedCRTHarmonic.GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ρ β p)ᶜ ≤
              ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨S, hS⟩ := h𝒮 γ hγ0 hγ2
  exact ⟨S, hS, lemma311Real_of_isValid hS hγ0 hγ2 hρ0 hρ1⟩

end MatedCRT.FirstPass.Derived
