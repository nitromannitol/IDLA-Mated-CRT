import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianMaximumGaussian

/-! # Finite-dimensional laws of continuous paths -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory

local instance : CompactSpace UnitTime := isCompact_iff_compactSpace.mp isCompact_Icc

variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E] [RegularSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Borel σ-algebra of continuous unit-interval paths is induced by the
product σ-algebra on their evaluations. -/
theorem unitPath_measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace C(UnitTime, E)) =
      MeasurableSpace.comap (fun f : C(UnitTime, E) => (f : UnitTime → E))
        (inferInstance : MeasurableSpace (UnitTime → E)) := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- Continuous path laws are determined by all finite-dimensional laws. -/
theorem unitPath_identDistrib_of_finite {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → C(UnitTime, E)}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ I : Finset UnitTime,
      IdentDistrib (fun ω => I.restrict (fun t => X ω t))
        (fun ω => I.restrict (fun t => Y ω t)) P P) :
    IdentDistrib X Y P P := by
  let e : C(UnitTime, E) → UnitTime → E := fun f => f
  have he : Measurable e := Measurable.of_eval fun t =>
    (continuous_eval_const t).measurable
  have hd : IdentDistrib (e ∘ X) (e ∘ Y) P P := by
    apply (identDistrib_iff_forall_finset_identDistrib
      (he.comp_aemeasurable hX) (he.comp_aemeasurable hY)).2
    exact h
  refine ⟨hX, hY, ?_⟩
  apply Measure.ext
  intro s hs
  have hs' : MeasurableSet[MeasurableSpace.comap e
      (inferInstance : MeasurableSpace (UnitTime → E))] s := by
    rw [← unitPath_measurableSpace_eq_comap]
    exact hs
  obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs'
  have hu' := congrArg (fun μ : Measure (UnitTime → E) => μ u) hd.map_eq
  rw [Measure.map_apply_of_aemeasurable (he.comp_aemeasurable hX) hu,
    Measure.map_apply_of_aemeasurable (he.comp_aemeasurable hY) hu] at hu'
  rw [Measure.map_apply_of_aemeasurable hX (he hu),
    Measure.map_apply_of_aemeasurable hY (he hu)]
  exact hu'

end MatedCRT
