import MatedCRT.Proposed.PrestonAnalytic2008
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Universal measurability of analytic sets on Polish spaces (transfer from Preston's Cantor-space theorem)

Source: Preston, arXiv:0809.3066v1. Theorem 6.1(1) (printed p. 35) gives, for a complete separable metric space `X` with its
Borel σ-algebra, an exactly measurable map `f : X → {0,1}^ℕ` with Borel range (`PrestonTheorem61Stmt`). An exactly measurable
map on a separated space is injective (Proposition 2.4, printed p. 8). Theorem 7.1 (printed p. 39) gives universal measurability
of analytic subsets of `{0,1}^ℕ` (`PrestonAnalyticCantorStmt`).

For an analytic `S ⊆ X`, the image `f '' S` is analytic in `{0,1}^ℕ` (`analyticSet_image_of_measurable`), hence universally
measurable. Since `f` is injective, `S = f ⁻¹' (f '' S)`, and the preimage of a null-measurable set under the measurable map `f`
is null-measurable for `μ` (`nullMeasurableSet_of_analyticSet_of_comap_eq`).

Only the exactness, the measurability and the injectivity of `f` are used. The Borel range `f(X) ∈ 𝓑` is part of the staged
Theorem 6.1 but is not needed for this direction. Both Preston inputs are explicit hypotheses; universal measurability is not
assumed.
-/

namespace MatedCRT

open MeasureTheory Function

/-- The image of an analytic set under a Borel-measurable map into a second countable space is analytic. Proof: write the
analytic set as the continuous image of a Polish space `Z`; the composite `f ∘ g` is Borel, so it is continuous for a finer
Polish topology on `Z` (`Measurable.exists_continuous`), and the image is the range of a continuous map. -/
theorem analyticSet_image_of_measurable {X Y : Type} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} (hf : Measurable f) {S : Set X}
    (hS : AnalyticSet S) : AnalyticSet (f '' S) := by
  obtain ⟨Z, tZ, hZ, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hS
  rw [← Set.range_comp]
  let _ : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨t', -, hcont, hpol⟩ := (hf.comp hg.measurable).exists_continuous
  exact analyticSet_iff_exists_polishSpace_range.2 ⟨Z, t', hpol, f ∘ g, hcont, rfl⟩

/-- Preston, Proposition 2.4 (printed p. 8): an exactly measurable map `f : (X, E) → (Y, F)` on a separated measurable space is
injective. Here `E` is separated because its singletons are measurable (`MeasurableSingletonClass`). Exactness is
`MeasurableSpace.comap f F = E`. Proof: if `x ≠ y` take a measurable `B ⊆ Y` with `f⁻¹(B) = {x}`; then `f x ∈ B`, and
`f y = f x` would give `y ∈ f⁻¹(B) = {x}`. -/
theorem injective_of_comap_eq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] {f : X → Y}
    (hf : MeasurableSpace.comap f (inferInstance : MeasurableSpace Y) = (inferInstance : MeasurableSpace X)) :
    Injective f := by
  intro x y hxy
  by_contra hne
  have hx : MeasurableSet[MeasurableSpace.comap f (inferInstance : MeasurableSpace Y)] ({x} : Set X) := by
    rw [hf]
    exact measurableSet_singleton x
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hx
  have hxB : x ∈ f ⁻¹' B := by
    rw [hB]
    exact Set.mem_singleton x
  have hyB : y ∈ f ⁻¹' B := by
    show f y ∈ B
    rw [← hxy]
    exact hxB
  rw [hB] at hyB
  exact hne (Set.mem_singleton_iff.1 hyB).symm

/-- Universal measurability of analytic sets transfers along an exactly measurable map `f : X → {0,1}^ℕ`: the analytic image
`f '' S` is universally measurable by Preston's Theorem 7.1 (`hCantor`), and `S = f ⁻¹' (f '' S)` by injectivity. -/
theorem nullMeasurableSet_of_analyticSet_of_comap_eq {X : Type} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (hCantor : PrestonAnalyticCantorStmt) {f : X → (ℕ → Bool)}
    (hf : MeasurableSpace.comap f (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) = (inferInstance : MeasurableSpace X))
    {S : Set X} (hS : AnalyticSet S) (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet S μ := by
  have hfm : Measurable f := Measurable.of_comap_le hf.le
  have hinj : Injective f := injective_of_comap_eq hf
  have hT : AnalyticSet (f '' S) := analyticSet_image_of_measurable hfm hS
  have hN : NullMeasurableSet (f '' S) (μ.map f) :=
    hCantor (f '' S) hT (μ.map f) inferInstance
  have hpre : NullMeasurableSet (f ⁻¹' (f '' S)) μ :=
    hN.preimage ⟨hfm, Measure.AbsolutelyContinuous.refl _⟩
  rwa [Set.preimage_image_eq S hinj] at hpre

/-- Preston's transfer: `PrestonAnalyticUniversallyMeasurableStmt` follows from the Cantor-space Theorem 7.1
(`PrestonAnalyticCantorStmt`) and the Polish form of Theorem 6.1 (`PrestonTheorem61Stmt`). For a Polish space `X` the
complete metric `m` compatible with its topology (`TopologicalSpace.IsCompletelyMetrizableSpace.complete`) supplies the input
of Theorem 6.1, and the Borel σ-algebra for the topology of `m` is the given one. -/
theorem prestonAnalyticUniversallyMeasurable_of_cantor (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) : PrestonAnalyticUniversallyMeasurableStmt := by
  intro X instT instP instM instB S hS μ hμ
  obtain ⟨m, hm, hcomp⟩ := (inferInstance : TopologicalSpace.IsCompletelyMetrizableSpace X).complete
  have hsep : @TopologicalSpace.SeparableSpace X m.toUniformSpace.toTopologicalSpace := by
    rw [hm]
    infer_instance
  have hB : @BorelSpace X m.toUniformSpace.toTopologicalSpace instM := by
    rw [hm]
    exact instB
  obtain ⟨-, f, hf, -⟩ := @hT61 X m hcomp hsep instM hB
  exact nullMeasurableSet_of_analyticSet_of_comap_eq hCantor hf hS μ

end MatedCRT
