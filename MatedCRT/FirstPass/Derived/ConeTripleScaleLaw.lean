import MatedCRT.FirstPass.Derived.ConeCurveScaleLaw
import MatedCRT.FirstPass.Derived.ConeBoundaryLengthScale
import MatedCRT.FirstPass.Derived.ConeCurveIndep

/-!
# Joint scaling law of the quantum cone, its space-filling SLE and the boundary-length pair

Let `(h, η, β)` be the `γ`-quantum cone `h = coneField X (coneRadial γ γ B B')` of a
mating-of-trees coupling, its space-filling SLE `η` parametrized by `γ`-LQG mass, and the
boundary-length pair `β`. For a level `b > 0` let `R_b = coneScale γ γ B B' b`,
`h_b = coneRescaleField γ R_b b h` and `η_b = coneRescaleCurve R_b b η = R_b⁻¹ η(b ·)`. Then

  `(h_b, η_b, b^{-1/2} β(b ·))` has the same law as `(h, η, β)`

on `Field × C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)` (`map_coneRescale_triple`; Duplantier-Miller-Sheffield,
Prop. 4.13(i) with Thm. 1.9).

The pair law of `ConeCurveScaleLaw` is stated for the curve as a function `ℝ → ℂ` with the
product sigma-algebra; on the set of continuous functions the passage to `C(ℝ, ℂ)` is
measurable, because pointwise evaluations generate the Borel sigma-algebra of `C(ℝ, ℂ)`
(`map_coneRescaleField_coneRescaleCurve`). The boundary-length pair is a Borel functional of the
field and the curve which intertwines the rescalings almost surely
(`exists_boundaryLength_rescaledPair`), so the triple law is the image of the pair law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling MatedCRTHarmonic.ConeScaling LQGMetric

/-- The cone scale radius of the mating-of-trees coupling is that of the cell model (the two
copies of the definitions have the same bodies). -/
theorem matedCRT_coneScale_eq_cellScaling (γ : ℝ) (b b' : ℝ≥0 → ℝ) (b₀ : ℝ) :
    MatedCRTHarmonic.MatedCRT.coneScale γ γ b b' b₀ = coneScale γ γ b b' b₀ := by
  unfold MatedCRTHarmonic.MatedCRT.coneScale MatedCRTHarmonic.CellScaling.coneScale
    MatedCRTHarmonic.MatedCRT.coneLogRadial MatedCRTHarmonic.CellScaling.coneLogRadial
    MatedCRTHarmonic.MatedCRT.lqgQ MatedCRTHarmonic.CellScaling.lqgQ
  rfl

/-- The rescaled cone field of the mating-of-trees coupling is that of the cell model. -/
theorem matedCRT_coneRescaleField_eq_cellScaling (γ R b₀ : ℝ) (f : DistC) :
    MatedCRTHarmonic.MatedCRT.coneRescaleField γ R b₀ f = coneRescaleField γ R b₀ f := by
  unfold MatedCRTHarmonic.MatedCRT.coneRescaleField MatedCRTHarmonic.CellScaling.coneRescaleField
    MatedCRTHarmonic.MatedCRT.lqgQ MatedCRTHarmonic.CellScaling.lqgQ
  rfl

open Classical in
/-- On the set of pairs whose second coordinate is continuous, replacing the function by the
corresponding element of `C(ℝ, ℂ)` is measurable. -/
theorem measurable_domRestrict_toContinuousMap {α : Type*} [MeasurableSpace α] :
    Measurable ({p : α × (ℝ → ℂ) | Continuous p.2}.domRestrict
      fun p => (p.1, if hc : Continuous p.2 then (⟨p.2, hc⟩ : C(ℝ, ℂ)) else 0)) := by
  have heq : ({p : α × (ℝ → ℂ) | Continuous p.2}.domRestrict
      fun p => (p.1, if hc : Continuous p.2 then (⟨p.2, hc⟩ : C(ℝ, ℂ)) else 0)) =
      fun x => (x.1.1, (⟨x.1.2, x.2⟩ : C(ℝ, ℂ))) := by
    funext x
    have hx : Continuous x.1.2 := x.2
    simp only [Set.domRestrict, hx, ↓reduceDIte]
  rw [heq]
  refine (measurable_fst.comp measurable_subtype_coe).prodMk ?_
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact (measurable_pi_apply t).comp (measurable_snd.comp measurable_subtype_coe)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- The cone scale radius `R_b` of a mating-of-trees coupling is almost everywhere measurable. -/
theorem aemeasurable_coneScale
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) (b₀ : ℝ) :
    AEMeasurable (fun ω => coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) P := by
  obtain ⟨W, hWm, -, hW⟩ := exists_radialPath_indepFun_igCurve h hγ hγ2
  exact (Real.measurable_exp.comp ((measurable_lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀)).comp
    hWm)).aemeasurable.congr (by
      filter_upwards [hW] with ω hω
      exact (coneScale_eq_exp_lastLevel γ b₀ hω).symm)

/-- The rescaled curve `(R, c) ↦ R⁻¹ c(b₀ ·)` is jointly measurable. -/
theorem measurable_coneRescaleCurve_uncurry (b₀ : ℝ) :
    Measurable fun p : ℝ × C(ℝ, ℂ) => MatedCRTHarmonic.MatedCRT.coneRescaleCurve p.1 b₀ p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  simp only [coe_coneRescaleCurve]
  exact ((Complex.measurable_ofReal.comp measurable_fst).inv).mul
    ((continuous_eval_const (b₀ * t)).measurable.comp measurable_snd)

open Classical in
/-- **Scaling law of the quantum cone and its space-filling SLE, continuous-curve form**: for
every level `b₀ > 0`, `(h_b, R_b⁻¹ η(b₀ ·))` has the law of `(h, η)` on `DistC × C(ℝ, ℂ)`. -/
theorem map_coneRescaleField_coneRescaleCurve
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b₀ : ℝ} (hb₀ : 0 < b₀) :
    P.map (fun ω =>
        (coneRescaleField γ (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀
            (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)),
          MatedCRTHarmonic.MatedCRT.coneRescaleCurve
            (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀ (η ω))) =
      P.map (fun ω => (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω), η ω)) := by
  have := h.isProbabilityMeasure
  have hlaw := map_coneRescaleField_curveScale h hγ hγ2 hb₀
  have hF := map_coneRescaleField_coneFieldOf hγ hγ2 h.gff h.bm_B h.bm_B'
    ⟨h.indep_cone.1, h.indep_cone.2⟩ b₀
  have hη : Measurable η := h.measurable_curves.2.1
  have hΦ : Measurable fun p : ℝ × C(ℝ, ℂ) => fun t : ℝ => ((p.1 : ℝ) : ℂ)⁻¹ * p.2 (b₀ * t) :=
    Measurable.of_eval fun t =>
      ((Complex.measurable_ofReal.comp measurable_fst).inv).mul
        ((continuous_eval_const (b₀ * t)).measurable.comp measurable_snd)
  have hRη := (aemeasurable_coneScale h hγ hγ2 b₀).prodMk hη.aemeasurable
  have hC := hΦ.comp_aemeasurable hRη
  have hY₁ := hF.2.1.prodMk hC
  have hY₂ : AEMeasurable (fun ω =>
      (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω), fun t : ℝ => η ω t)) P :=
    hF.1.prodMk (Measurable.of_eval fun t =>
      (continuous_eval_const t).measurable.comp hη).aemeasurable
  have key := LatticeProb.map_comp_eq_of_map_eq_of_ae_mem hY₁ hY₂ hlaw
    (ae_of_all _ fun ω => continuous_const.mul ((η ω).continuous.comp
      (continuous_const.mul continuous_id)))
    (ae_of_all _ fun ω => (η ω).continuous) (measurable_domRestrict_toContinuousMap (α := DistC))
  refine (congrArg (fun F => P.map F) ?_).trans (key.trans (congrArg (fun F => P.map F) ?_))
  · funext ω
    have hc : Continuous fun t : ℝ =>
        ((coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀ : ℝ) : ℂ)⁻¹ * η ω (b₀ * t) :=
      continuous_const.mul ((η ω).continuous.comp (continuous_const.mul continuous_id))
    refine Prod.ext rfl ?_
    simp only [Function.comp_apply, hc, ↓reduceDIte]
    ext1 s
    simp only [coe_coneRescaleCurve, ContinuousMap.coe_mk]
  · funext ω
    have hc : Continuous fun t : ℝ => η ω t := (η ω).continuous
    refine Prod.ext rfl ?_
    simp only [hc, ↓reduceDIte]
    rfl

/-- **Joint scaling law of the quantum cone, its space-filling SLE and its boundary-length
pair** (Duplantier-Miller-Sheffield, Prop. 4.13(i) with Thm. 1.9): for every level `b₀ > 0`,
`(h_b, R_b⁻¹ η(b₀ ·), b₀^{-1/2} β(b₀ ·))` has the law of `(h, η, β)`. -/
theorem map_coneRescale_triple
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b₀ : ℝ} (hb₀ : 0 < b₀) :
    P.map (fun ω =>
        (coneRescaleField γ (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀
            (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)),
          MatedCRTHarmonic.MatedCRT.coneRescaleCurve
            (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀ (η ω),
          rescaledPair b₀ (bm ω))) =
      P.map (fun ω => (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω), η ω, bm ω)) := by
  have := h.isProbabilityMeasure
  obtain ⟨BL, hBL, hbm, hsc⟩ := exists_boundaryLength_rescaledPair h
  simp only [MatedCRT.FirstPass.Derived.matedCRT_coneField_coneRadial_eq, matedCRT_coneScale_eq_cellScaling,
    matedCRT_coneRescaleField_eq_cellScaling] at hbm hsc
  let G : DistC × C(ℝ, ℂ) → DistC × C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2 :=
    fun p => (p.1, p.2, BL p)
  have hG : Measurable G := measurable_fst.prodMk (measurable_snd.prodMk hBL)
  have hF := map_coneRescaleField_coneFieldOf hγ hγ2 h.gff h.bm_B h.bm_B'
    ⟨h.indep_cone.1, h.indep_cone.2⟩ b₀
  have hη : Measurable η := h.measurable_curves.2.1
  have hRη := (aemeasurable_coneScale h hγ hγ2 b₀).prodMk hη.aemeasurable
  have hC := (measurable_coneRescaleCurve_uncurry b₀).comp_aemeasurable hRη
  have hZ₁ : AEMeasurable (fun ω =>
      (coneRescaleField γ (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀
          (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)),
        MatedCRTHarmonic.MatedCRT.coneRescaleCurve
          (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀ (η ω))) P :=
    hF.2.1.prodMk hC
  have hZ₂ : AEMeasurable (fun ω =>
      (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω), η ω)) P :=
    hF.1.prodMk hη.aemeasurable
  have key := congrArg (fun μ : Measure (DistC × C(ℝ, ℂ)) => μ.map G)
    (map_coneRescaleField_coneRescaleCurve h hγ hγ2 hb₀)
  rw [AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hZ₁,
    AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hZ₂] at key
  refine (Measure.map_congr ?_).trans (key.trans (Measure.map_congr ?_))
  · filter_upwards [hsc b₀ hb₀] with ω hω
    exact Prod.ext rfl (Prod.ext rfl hω.symm)
  · filter_upwards [hbm] with ω hω
    exact Prod.ext rfl (Prod.ext rfl hω.symm)

end MatedCRT.Sec1
