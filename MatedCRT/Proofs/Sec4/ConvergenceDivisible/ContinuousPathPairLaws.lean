import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianFiniteRotation

/-! # Finite-dimensional laws of pairs of continuous paths -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory

local instance : CompactSpace UnitTime := isCompact_iff_compactSpace.mp isCompact_Icc

/-- Joint laws of continuous path pairs are determined by their finite joint laws. -/
theorem unitPath_pair_identDistrib_of_finite {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → C(UnitTime, ℝ) × C(UnitTime, ℝ)}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ I : Finset UnitTime,
      IdentDistrib (fun ω => (I.restrict (fun t => (X ω).1 t),
          I.restrict (fun t => (X ω).2 t)))
        (fun ω => (I.restrict (fun t => (Y ω).1 t),
          I.restrict (fun t => (Y ω).2 t))) P P) :
    IdentDistrib X Y P P := by
  let pack : C(UnitTime, ℝ) × C(UnitTime, ℝ) → C(UnitTime, ℝ × ℝ) :=
    fun p => p.1.prodMk p.2
  let unpack : C(UnitTime, ℝ × ℝ) → C(UnitTime, ℝ) × C(UnitTime, ℝ) :=
    fun f => (ContinuousMap.fst.comp f, ContinuousMap.snd.comp f)
  have hp : Measurable pack := ContinuousMap.measurable_iff_eval.2 fun t =>
    ((continuous_eval_const t).measurable.comp measurable_fst).prodMk
      ((continuous_eval_const t).measurable.comp measurable_snd)
  have hu : Measurable unpack := by
    apply Measurable.prodMk
    · apply ContinuousMap.measurable_iff_eval.2
      intro t
      exact measurable_fst.comp (continuous_eval_const t).measurable
    · apply ContinuousMap.measurable_iff_eval.2
      intro t
      exact measurable_snd.comp (continuous_eval_const t).measurable
  have hpack : IdentDistrib (pack ∘ X) (pack ∘ Y) P P := by
    apply unitPath_identDistrib_of_finite (hp.comp_aemeasurable hX)
      (hp.comp_aemeasurable hY)
    intro I
    let merge : (I → ℝ) × (I → ℝ) → I → ℝ × ℝ :=
      fun p t => (p.1 t, p.2 t)
    have hm : Measurable merge := Measurable.of_eval fun t =>
      (measurable_pi_apply t |>.comp measurable_fst).prodMk
        (measurable_pi_apply t |>.comp measurable_snd)
    exact (h I).comp hm
  have hback := hpack.comp hu
  have hundo (p : C(UnitTime, ℝ) × C(UnitTime, ℝ)) : unpack (pack p) = p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext <;> ext t <;> rfl
  convert hback using 1 <;> funext ω <;> exact (hundo _).symm

end MatedCRT
