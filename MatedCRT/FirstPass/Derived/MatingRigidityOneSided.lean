import MatedCRT.FirstPass.Derived.MatingRelation

/-!
# One-sided mating rigidity

`MatingRigidOn G` (in `MatingRelation`) asks that, for pairs in `G`, *equal* mating relations force equal
boundary-length pairs up to the swap `L ↔ R`. To use it for a second random pair `Y`, one needs the mating relation
of `Y` to be the fibre relation of the space-filling curve `η`, that is both facts (P1) (`merge`: every direct
identification of `Y` merges `η`) and (P2) (`onlyMerge`: `η` merges only times related by `Y`) of DMS14 Lemmas 8.8
and 8.14 for `Y`.

The one-sided form `MatingRigidLEOn G` asks instead that, for pairs `b, b'` in `G`, *inclusion* of the mating
relation of `b` in that of `b'` already forces `b' = b` up to the swap. Then (P1) for `Y` suffices: by (P1) the
mating relation of `Y` is contained in the fibre relation of `η`, which is almost surely the mating relation of the
boundary-length pair `bm` of the environment itself. No version of (P2) for `Y` is used.

* `matingRel_le_fibre_of_merge`: (P1) alone puts the mating relation inside the fibre relation.
* `MatingRigidLEOn`, `MatingRigidLEOn.matingRigidOn`: the one-sided form implies the two-sided one.
* `MatedCRTEnv.IsValid.ae_mult_eq_of_matingRigidLEOn` (for any continuous version `η'` of the curve) and
  `MatedCRTEnv.IsValid.ae_mult_eq_of_matingRigidLEOn_self` (for `η` itself): the edge multiplicity of a valid
  environment is almost surely the mated-CRT edge count of `Y`.
-/

namespace MatedCRT

open MeasureTheory

/-- If every direct `L`- or `R`-identification of `b` merges the curve `η` (fact (P1) of DMS14 Lemma 8.8), then any
two times related by the mating relation of `b` lie in the same fibre of `η`. -/
theorem matingRel_le_fibre_of_merge {α : Type*} {b : MatedCRTHarmonic.MatedCRT.Path2} {η : ℝ → α}
    (hmerge : ∀ s t : ℝ, (MatedCRTHarmonic.MatedCRT.DirectRel
        (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u b) s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u b) s t) → η s = η t)
    {s t : ℝ} (h : matingRel b s t) : η s = η t := by
  induction h with
  | rel a c hac => exact hmerge a c hac
  | refl a => rfl
  | symm a c _ ih => exact ih.symm
  | trans a c d _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **One-sided mating rigidity on a set of pairs**: for pairs `b, b' ∈ G`, if every pair of times related by the
mating relation of `b` is related by that of `b'`, then `b' = b` or `b'` equals `b` after the swap `L ↔ R`. -/
def MatingRigidLEOn (G : Set MatedCRTHarmonic.MatedCRT.Path2) : Prop :=
  ∀ b ∈ G, ∀ b' ∈ G, (∀ s t : ℝ, matingRel b s t → matingRel b' s t) →
    (∀ u, MatedCRTHarmonic.MatedCRT.lrCoord 0 u b' = MatedCRTHarmonic.MatedCRT.lrCoord 0 u b ∧
        MatedCRTHarmonic.MatedCRT.lrCoord 1 u b' = MatedCRTHarmonic.MatedCRT.lrCoord 1 u b) ∨
    (∀ u, MatedCRTHarmonic.MatedCRT.lrCoord 0 u b' = MatedCRTHarmonic.MatedCRT.lrCoord 1 u b ∧
        MatedCRTHarmonic.MatedCRT.lrCoord 1 u b' = MatedCRTHarmonic.MatedCRT.lrCoord 0 u b)

/-- One-sided mating rigidity implies mating rigidity. -/
theorem MatingRigidLEOn.matingRigidOn {G : Set MatedCRTHarmonic.MatedCRT.Path2} (hG : MatingRigidLEOn G) :
    MatingRigidOn G := by
  intro b hb b' hb' h
  refine hG b hb b' hb' fun s t hst => ?_
  rw [← h]
  exact hst

/-- **One-sided rigidity transfer.** Let `G` be a one-sided mating-rigid set of pairs whose complement is null for
every law of a `γ`-correlated two-sided Brownian motion. For a valid environment, a continuous version `η'` of its
space-filling curve, and a random pair `Y` that lies almost surely in `G` and whose direct identifications almost
surely merge `η'` (fact (P1) for `Y`), the edge multiplicity is almost surely the mated-CRT edge count of `Y`. -/
theorem MatedCRTEnv.IsValid.ae_mult_eq_of_matingRigidLEOn {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) {η' : Ω → C(ℝ, ℂ)} (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {Y : Ω → MatedCRTHarmonic.MatedCRT.Path2} (hYG : ∀ᵐ ω ∂S.P, Y ω ∈ G)
    (hY : ∀ᵐ ω ∂S.P, ∀ s t : ℝ,
      (MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u (Y ω)) s t ∨
        MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u (Y ω)) s t) →
        η' ω s = η' ω t)
    (ε : ℝ) :
    ∀ᵐ ω ∂S.P, S.mult ε ω = bmEdgeCount ε (fun t => (Y ω t).1) (fun t => (Y ω t).2) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηw, η₀, hC, -⟩ := hS.matingOfTrees
  filter_upwards [hS.ae_matingRel_eq_fibre, ae_mem_of_correlatedBM2_null hC hGnull, hYG, hY, hη']
    with ω h₁ h₂ h₃ h₄ h₅
  refine S.mult_eq_of_eq_or_swap ε ω (hG _ h₃ _ h₂ fun s t hst => ?_)
  rw [h₁]
  have h₆ : η' ω s = η' ω t := matingRel_le_fibre_of_merge (η := fun u => η' ω u) h₄ hst
  show S.η ω s = S.η ω t
  rw [← h₅]
  exact h₆

/-- **One-sided rigidity transfer**, with fact (P1) for `Y` stated for the curve `η` of the environment itself. -/
theorem MatedCRTEnv.IsValid.ae_mult_eq_of_matingRigidLEOn_self {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) {Y : Ω → MatedCRTHarmonic.MatedCRT.Path2} (hYG : ∀ᵐ ω ∂S.P, Y ω ∈ G)
    (hY : ∀ᵐ ω ∂S.P, ∀ s t : ℝ,
      (MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u (Y ω)) s t ∨
        MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u (Y ω)) s t) →
        S.η ω s = S.η ω t)
    (ε : ℝ) :
    ∀ᵐ ω ∂S.P, S.mult ε ω = bmEdgeCount ε (fun t => (Y ω t).1) (fun t => (Y ω t).2) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηw, η₀, hC, -⟩ := hS.matingOfTrees
  filter_upwards [hS.ae_matingRel_eq_fibre, ae_mem_of_correlatedBM2_null hC hGnull, hYG, hY]
    with ω h₁ h₂ h₃ h₄
  refine S.mult_eq_of_eq_or_swap ε ω (hG _ h₃ _ h₂ fun s t hst => ?_)
  rw [h₁]
  exact matingRel_le_fibre_of_merge (η := S.η ω) h₄ hst

end MatedCRT
