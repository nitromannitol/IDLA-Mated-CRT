import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Borel factor of a graph (Lusin-Souslin), first pass S2i

Measure-theoretic lemma behind the factorizations `ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`) and
`ConeGlobalFamilyFactorStep` (`FirstPass/S2g/ScaleInvariance.lean`): a Borel set `S` of a product of two standard Borel
spaces which is the graph of a relation (its fibres over the first coordinate are at most singletons) is the graph of a
Borel function `F`, defined on its projection `B`, which is itself Borel. The proof is the Lusin-Souslin theorem
(`Measurable.measurableEmbedding`) for the first projection restricted to `S`, which is injective on `S`. -/

namespace MatedCRT

open MeasureTheory Set

/-- `S` is the graph of a relation: over each first coordinate there is at most one second coordinate. -/
def IsGraphSet {E Y : Type*} (S : Set (E × Y)) : Prop :=
  ∀ x y y', (x, y) ∈ S → (x, y') ∈ S → y = y'

/-- **Borel factor of a Borel graph (Lusin-Souslin).** For a Borel graph `S ⊆ E × Y` of standard Borel spaces there are a
Borel set `B ⊆ E` (the projection of `S`) and a Borel map `F : E → Y` with `S = {(x, F x) : x ∈ B}`: every `(x, F x)`
with `x ∈ B` lies in `S`, and every point of `S` has the form `(x, F x)` with `x ∈ B`. -/
theorem exists_measurable_graph_factor {E Y : Type*} [MeasurableSpace E] [MeasurableSpace Y]
    [StandardBorelSpace E] [StandardBorelSpace Y] [Nonempty Y]
    {S : Set (E × Y)} (hS : MeasurableSet S) (hgraph : IsGraphSet S) :
    ∃ (B : Set E) (F : E → Y), MeasurableSet B ∧ Measurable F ∧ (∀ x ∈ B, (x, F x) ∈ S) ∧
      ∀ x y, (x, y) ∈ S → x ∈ B ∧ y = F x := by
  have : StandardBorelSpace S := hS.standardBorel
  let f : S → E := fun s => s.1.1
  let g : S → Y := fun s => s.1.2
  have hf : Measurable f := measurable_fst.comp measurable_subtype_coe
  have hg : Measurable g := measurable_snd.comp measurable_subtype_coe
  have hinj : Function.Injective f := by
    rintro ⟨⟨x, y⟩, hs⟩ ⟨⟨x', y'⟩, hs'⟩ h
    simp only [f] at h
    subst h
    have hyy : y = y' := hgraph x y y' hs hs'
    subst hyy
    rfl
  have hemb : MeasurableEmbedding f := hf.measurableEmbedding hinj
  obtain ⟨F, hFm, hF⟩ := hemb.exists_measurable_extend hg (fun _ => inferInstance)
  refine ⟨range f, F, hemb.measurableSet_range, hFm, ?_, ?_⟩
  · rintro x ⟨s, rfl⟩
    have hFs : F (f s) = g s := congrFun hF s
    rw [hFs]
    exact s.2
  · intro x y hxy
    let s : S := ⟨(x, y), hxy⟩
    have hFs : F (f s) = g s := congrFun hF s
    refine ⟨⟨s, rfl⟩, ?_⟩
    have hx : f s = x := rfl
    rw [← hx, hFs]

end MatedCRT
