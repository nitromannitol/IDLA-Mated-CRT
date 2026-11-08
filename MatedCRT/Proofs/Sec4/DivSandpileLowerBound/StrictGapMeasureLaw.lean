import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Dominating laws of locally finite measures through open masses -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- Domination of the joint laws of all open-set masses implies domination of
    the laws of locally finite random measures. -/
theorem measureLaw_absolutelyContinuous_of_openMassLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → Measure ℂ} {Y : Ω' → Measure ℂ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hXloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (X ω))
    (hYloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (Y ω))
    (hdom : P.map (fun ω (U : {U : Set ℂ // IsOpen U}) => X ω U.1) ≪
      Q.map (fun ω (U : {U : Set ℂ // IsOpen U}) => Y ω U.1)) :
    P.map X ≪ Q.map Y := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  let F : Measure ℂ → O → ℝ≥0∞ := fun m U => m U.1
  have hF : Measurable F := Measurable.of_eval fun U => Measure.measurable_coe U.2.measurableSet
  let L := {m : Measure ℂ // IsLocallyFiniteMeasure m}
  let e : L → O → ℝ≥0∞ := fun m => F m.1
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hcoe : Measurable (Subtype.val : L → Measure ℂ) := by
    apply measurable_measure_of_isOpen (fun m => m.2)
    intro U hU
    exact (measurable_pi_apply (⟨U, hU⟩ : O)).comp (comap_measurable e)
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hnull
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hcoe hS)
  have hpreX : X ⁻¹' S =ᵐ[P] (F ∘ X) ⁻¹' T := by
    filter_upwards [hXloc] with ω hω
    change (X ω ∈ S) = (F (X ω) ∈ T)
    exact propext (Set.ext_iff.mp heq (⟨X ω, hω⟩ : L)).symm
  have hpreY : Y ⁻¹' S =ᵐ[Q] (F ∘ Y) ⁻¹' T := by
    filter_upwards [hYloc] with ω hω
    change (Y ω ∈ S) = (F (Y ω) ∈ T)
    exact propext (Set.ext_iff.mp heq (⟨Y ω, hω⟩ : L)).symm
  rw [Measure.map_apply_of_aemeasurable hY hS, measure_congr hpreY,
    ← Measure.map_apply_of_aemeasurable (hF.comp_aemeasurable hY) hT] at hnull
  rw [Measure.map_apply_of_aemeasurable hX hS, measure_congr hpreX,
    ← Measure.map_apply_of_aemeasurable (hF.comp_aemeasurable hX) hT]
  exact hdom hnull

/-- A common family of measurable open-mass decoders transfers domination of
    field laws to domination of locally finite measure laws. The decoder for
    each open set may have its own null set. -/
theorem measureLaw_absolutelyContinuous_of_openMassDecoders
    {Ω Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace V]
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {X : Ω → Measure ℂ} {Y : Ω' → Measure ℂ} {Z : Ω → V} {W : Ω' → V}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hXloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (X ω))
    (hYloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (Y ω))
    (hZ : Measurable Z) (hW : Measurable W) (hdom : P.map Z ≪ Q.map W)
    (hdec : ∀ U : Set ℂ, IsOpen U → ∃ d : V → ℝ≥0∞, Measurable d ∧
      (∀ᵐ ω ∂P, X ω U = d (Z ω)) ∧ (∀ᵐ ω ∂Q, Y ω U = d (W ω))) :
    P.map X ≪ Q.map Y := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  choose d hdm hdx hdy using fun U : O => hdec U.1 U.2
  let D : V → O → ℝ≥0∞ := fun v U => d U v
  have hD : Measurable D := Measurable.of_eval hdm
  let F : Measure ℂ → O → ℝ≥0∞ := fun μ U => μ U.1
  have hF : Measurable F := Measurable.of_eval fun U => Measure.measurable_coe U.2.measurableSet
  have hPX : P.map (F ∘ X) = P.map (D ∘ Z) := by
    apply map_eq_of_forall_ae_eq (hF.comp_aemeasurable hX) (hD.comp hZ).aemeasurable
    intro U
    exact hdx U
  have hQY : Q.map (F ∘ Y) = Q.map (D ∘ W) := by
    apply map_eq_of_forall_ae_eq (hF.comp_aemeasurable hY) (hD.comp hW).aemeasurable
    intro U
    exact hdy U
  apply measureLaw_absolutelyContinuous_of_openMassLaw hX hY hXloc hYloc
  change P.map (F ∘ X) ≪ Q.map (F ∘ Y)
  rw [hPX, hQY, ← Measure.map_map hD hZ, ← Measure.map_map hD hW]
  exact hdom.map hD

end MatedCRT
