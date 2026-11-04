import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousPathPairLaws

/-! # Rotation invariance of the Brownian unit-path law -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

local instance : CompactSpace UnitTime := isCompact_iff_compactSpace.mp isCompact_Icc

/-- The product of two Brownian unit-path laws is invariant under rotation. -/
theorem brownian_unit_path_rotation (θ : ℝ) :
    let μ := (brownianMotion 0).map unitPathRestriction
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  let μ := (brownianMotion 0).map unitPathRestriction
  let P := μ.prod μ
  let R : (C(UnitTime, ℝ) × C(UnitTime, ℝ)) →L[ℝ]
      (C(UnitTime, ℝ) × C(UnitTime, ℝ)) := ContinuousLinearMap.rotation θ
  have hpair : IdentDistrib R id P P := by
    apply unitPath_pair_identDistrib_of_finite R.continuous.aemeasurable
      measurable_id.aemeasurable
    intro I
    let F : C(UnitTime, ℝ) → I → ℝ := fun f => I.restrict f
    let Q : (C(UnitTime, ℝ) × C(UnitTime, ℝ)) → (I → ℝ) × (I → ℝ) :=
      fun p => (F p.1, F p.2)
    let r : ((I → ℝ) × (I → ℝ)) →L[ℝ] ((I → ℝ) × (I → ℝ)) :=
      ContinuousLinearMap.rotation θ
    have hF : Measurable F := Measurable.of_eval fun t =>
      (continuous_eval_const t.1).measurable
    have hQ : Measurable Q := (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
    have hcomm : Q ∘ R = r ∘ Q := by
      funext p
      apply Prod.ext <;> ext t <;>
        simp [Q, F, R, r, ContinuousLinearMap.rotation_apply]
    have hmap : P.map Q = (μ.map F).prod (μ.map F) := by
      symm
      exact Measure.map_prod_map μ μ hF hF
    have hfinite : ((μ.map F).prod (μ.map F)).map r = (μ.map F).prod (μ.map F) := by
      have h := unitPathRestriction_finite_rotation I θ
      simpa [μ, Measure.map_map hF continuous_unitPathRestriction.measurable, F,
        Function.comp_def, r] using h
    refine ⟨(hQ.comp R.continuous.measurable).aemeasurable,
      hQ.aemeasurable, ?_⟩
    change P.map (Q ∘ R) = P.map Q
    rw [hcomm, ← Measure.map_map r.continuous.measurable hQ, hmap, hfinite]
  simpa [P, R] using hpair.map_eq

end MatedCRT
