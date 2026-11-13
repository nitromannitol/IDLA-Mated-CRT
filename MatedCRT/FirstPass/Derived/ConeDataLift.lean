import MatedCRT.FirstPass.Derived.ConeRadialUniform
import MatedCRT.FirstPass.Derived.ConeTripleScaleLaw
import LatticeProb.Prob.SameSpaceLift

/-!
# The coupling data of the rescaled cone on the sample space of the environment

Let `S` be a valid environment and `V` the data of its mating-of-trees coupling: the whole-plane
GFF `X`, the radial Brownian motions `B, B'` of the `γ`-quantum cone `h = coneField X (coneRadial γ γ B B')`,
the curve `η` (parametrized by `μ_h`-area) and the boundary-length pair `β`, with `η` the curve of
`S`, `h` the field of `S` and `β` the boundary-length pair of `S`.

For a level `b > 0` let `R_b` be the cone scale. The rescaled triple
`Y = (h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` has the law of `(h, η, β)` (Duplantier-Miller-Sheffield,
Prop. 4.13(i) with Thm. 1.9). It is a Borel function of the quadruple
`(lateral part of X, (B, B'), η, β)`, so it is independent of the uniform variable
`Z = radialUniform X` (the pairing of `X` with a radial test function, which is independent of the
lateral part of `X`). The same-space lift (`ProbabilityTheory.exists_map_eq_and_ae_comp_eq`, applied
to the law of `V` and the map `coneTriple γ`) then gives a random element `V'` of the data space,
on the sample space of `S`, with the law of `V` and with `coneTriple γ V' = Y` almost surely: the
coupling data of the rescaled cone.

Main results:
* `MatedCRTEnv.IsValid.exists_couplingData_tied`: the coupling of a valid environment is given by a
  measurable random element of the data space.
* `IsCouplingData.map_coneRescaleOfQuad`: the law of the rescaled triple.
* `MatedCRTEnv.IsValid.exists_coneDataLift`: the lifted data `V'`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT

/-- The cone scale `R_b` as a function of the pair of radial Brownian paths: the exponential of the
last level `γ⁻¹ log b` of the radial path of the cone. -/
noncomputable def coneScaleOfPair (γ b : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : ℝ :=
  Real.exp (MatedCRTHarmonic.ConeScaling.lastLevel (MatedCRTHarmonic.MatedCRT.lqgQ γ)
    (γ⁻¹ * Real.log b) (MatedCRTHarmonic.ConeScaling.radMap γ γ p))

theorem measurable_coneScaleOfPair (γ b : ℝ) : Measurable (coneScaleOfPair γ b) :=
  Real.measurable_exp.comp ((MatedCRTHarmonic.ConeScaling.measurable_lastLevel _ _).comp
    (MatedCRTHarmonic.ConeScaling.measurable_radMap γ γ))

theorem coneScaleOf_eq_coneScaleOfPair (γ b : ℝ) (v : MatedCRTHarmonic.MatedCRT.CouplingData) :
    MatedCRTHarmonic.MatedCRT.CouplingData.coneScaleOf γ b v = coneScaleOfPair γ b (v.B, v.B') :=
  rfl

/-- The quadruple `(lateral part of X, (B, B'), η, β)` read off the data. -/
noncomputable def coneQuad (v : MatedCRTHarmonic.MatedCRT.CouplingData) :
    LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2 :=
  (MatedCRTHarmonic.CellScaling.lateralPart v.X, (v.B, v.B'), v.η, v.bm)

theorem measurable_coneQuad : Measurable coneQuad :=
  (MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_X).prodMk
    ((MatedCRTHarmonic.MatedCRT.CouplingData.measurable_B.prodMk
        MatedCRTHarmonic.MatedCRT.CouplingData.measurable_B').prodMk
      (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk
        MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm))

/-- The rescaled triple `(h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` as a function of the quadruple
`(lateral part of X, (B, B'), η, β)`: the cone field is rebuilt from the lateral part and the radial
paths, and `R_b` is read off the radial paths. -/
noncomputable def coneRescaleOfQuad (γ b : ℝ)
    (q : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) :
    MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2 :=
  (MatedCRTHarmonic.MatedCRT.coneRescaleField γ (coneScaleOfPair γ b q.2.1) b
      (coneFieldOfLateral γ (q.1, q.2.1)),
    MatedCRTHarmonic.MatedCRT.coneRescaleCurve (coneScaleOfPair γ b q.2.1) b q.2.2.1,
    MatedCRTHarmonic.MatedCRT.brownRescale b q.2.2.2)

/-- The space of quadruples `(lateral field, (B, B'), η, β)`. -/
abbrev QuadT := LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2

theorem measurable_coneScaleOfPair_quad (γ b : ℝ) :
    Measurable fun q : QuadT => coneScaleOfPair γ b q.2.1 :=
  (measurable_coneScaleOfPair γ b).comp (measurable_fst.comp measurable_snd)

theorem measurable_coneFieldOfLateral_quad (γ : ℝ) :
    Measurable fun q : QuadT => coneFieldOfLateral γ (q.1, q.2.1) :=
  (measurable_coneFieldOfLateral γ).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

theorem measurable_coneRescaleOfQuad_fst (γ b : ℝ) :
    Measurable fun q : QuadT => MatedCRTHarmonic.MatedCRT.coneRescaleField γ
      (coneScaleOfPair γ b q.2.1) b (coneFieldOfLateral γ (q.1, q.2.1)) := by
  have hR := measurable_coneScaleOfPair_quad γ b
  have hA : Measurable fun q : QuadT =>
      LQGMetric.affineComp (coneScaleOfPair γ b q.2.1) 0 (coneFieldOfLateral γ (q.1, q.2.1)) :=
    MatedCRTHarmonic.MoTPort.ConeMeas.measurable_affineComp_joint.comp
      (hR.prodMk (measurable_coneFieldOfLateral_quad γ))
  unfold MatedCRTHarmonic.MatedCRT.coneRescaleField
  exact MatedCRTHarmonic.MatedCRT.measurable_addConst_comp hA
    ((measurable_const.mul (Real.measurable_log.comp hR)).sub measurable_const)

theorem measurable_coneRescaleOfQuad_snd (γ b : ℝ) :
    Measurable fun q : QuadT => MatedCRTHarmonic.MatedCRT.coneRescaleCurve
      (coneScaleOfPair γ b q.2.1) b q.2.2.1 :=
  (MatedCRTHarmonic.MatedCRT.measurable_coneRescaleCurve_uncurry b).comp
    ((measurable_coneScaleOfPair_quad γ b).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))

theorem measurable_coneRescaleOfQuad_thd (b : ℝ) :
    Measurable fun q : QuadT => MatedCRTHarmonic.MatedCRT.brownRescale b q.2.2.2 :=
  (MatedCRTHarmonic.MatedCRT.measurable_brownRescale b).comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_coneRescaleOfQuad (γ b : ℝ) : Measurable (coneRescaleOfQuad γ b) :=
  (measurable_coneRescaleOfQuad_fst γ b).prodMk
    ((measurable_coneRescaleOfQuad_snd γ b).prodMk (measurable_coneRescaleOfQuad_thd b))

/-- On `radGood` the rescaled triple of the quadruple of the data is
`(h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` with `h = coneField X (coneRadial γ γ B B')` and
`R_b = coneScale γ γ B B' b`. -/
theorem coneRescaleOfQuad_coneQuad {γ : ℝ} {v : MatedCRTHarmonic.MatedCRT.CouplingData}
    (hv : (v.B, v.B') ∈ MatedCRTHarmonic.ConeScaling.radGood γ γ) (b : ℝ) :
    coneRescaleOfQuad γ b (coneQuad v) =
      (MatedCRTHarmonic.MatedCRT.coneRescaleField γ
          (MatedCRTHarmonic.MatedCRT.coneScale γ γ v.B v.B' b) b
          (MatedCRTHarmonic.MatedCRT.coneField v.X (MatedCRTHarmonic.MatedCRT.coneRadial γ γ v.B v.B')),
        MatedCRTHarmonic.MatedCRT.coneRescaleCurve
          (MatedCRTHarmonic.MatedCRT.coneScale γ γ v.B v.B' b) b v.η,
        MatedCRTHarmonic.MatedCRT.brownRescale b v.bm) := by
  have hR : coneScaleOfPair γ b (v.B, v.B') = MatedCRTHarmonic.MatedCRT.coneScale γ γ v.B v.B' b :=
    (MatedCRTHarmonic.MatedCRT.CouplingData.coneScale_eq_coneScaleOf hv b).symm
  have hF : coneFieldOfLateral γ (MatedCRTHarmonic.CellScaling.lateralPart v.X, (v.B, v.B')) =
      MatedCRTHarmonic.MatedCRT.coneField v.X (MatedCRTHarmonic.MatedCRT.coneRadial γ γ v.B v.B') :=
    MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple_fst_of_mem hv
  show (MatedCRTHarmonic.MatedCRT.coneRescaleField γ (coneScaleOfPair γ b (v.B, v.B')) b
      (coneFieldOfLateral γ (MatedCRTHarmonic.CellScaling.lateralPart v.X, (v.B, v.B'))),
    MatedCRTHarmonic.MatedCRT.coneRescaleCurve (coneScaleOfPair γ b (v.B, v.B')) b v.η,
    MatedCRTHarmonic.MatedCRT.brownRescale b v.bm) = _
  rw [hR, hF]

/-- **Law of the rescaled triple of the data** (Duplantier-Miller-Sheffield, Prop. 4.13(i) with
Thm. 1.9): for the data `V` of a mating-of-trees coupling and a level `b > 0`, the rescaled triple
`(h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` has the law of `coneTriple γ V = (h, η, β)`. -/
theorem IsCouplingData.map_coneRescaleOfQuad {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {V : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hC : MatedCRTHarmonic.MatedCRT.IsCouplingData γ P V) (hV : Measurable V) (hγ : 0 < γ)
    (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b) :
    P.map (fun ω => coneRescaleOfQuad γ b (coneQuad (V ω))) =
      (P.map V).map (MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ) := by
  have hCP := (show MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _
    from hC)
  have key := Sec1.map_coneRescale_triple hCP hγ hγ2 hb
  rw [Measure.map_map (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_coneTriple γ) hV]
  refine (Measure.map_congr ?_).trans (key.trans (Measure.map_congr ?_))
  · filter_upwards [hC.ae_radGood hγ hγ2] with ω hω
    rw [coneRescaleOfQuad_coneQuad hω b, Sec1.matedCRT_coneRescaleField_eq_cellScaling,
      Sec1.matedCRT_coneScale_eq_cellScaling, FirstPass.Derived.matedCRT_coneField_coneRadial_eq,
      Sec1.brownRescale_eq_rescaledPair hb]
  · filter_upwards [hC.ae_radGood hγ hγ2] with ω hω
    exact Prod.ext ((MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple_fst_of_mem hω).trans
      (FirstPass.Derived.matedCRT_coneField_coneRadial_eq γ _ _ _)).symm rfl

/-- The mating-of-trees coupling of a valid environment is given by a measurable random element `V`
of the data space: `V` is coupling data, its boundary-length pair is that of the environment, and
almost surely its curve is the curve of the environment and its cone field
`coneField X (coneRadial γ γ B B')` has the pairings of the field of the environment. -/
theorem MatedCRTEnv.IsValid.exists_couplingData_tied {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ V : Ω → MatedCRTHarmonic.MatedCRT.CouplingData, Measurable V ∧
      MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V ∧ (∀ ω, (V ω).bm = S.bm ω) ∧
      ∀ᵐ ω ∂S.P, ⇑(V ω).η = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (V ω).X
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') φ := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨V, hV, hC, hco, hVae⟩ := hMoT.exists_couplingData
  refine ⟨V, hV, hC, fun ω => (hco ω).2.2.2.2.2.2, ?_⟩
  filter_upwards [hae, hVae] with ω h1 h2
  have hB : (fun u => B u ω) = ⇑(V ω).B := funext fun u => (h2.1 u).symm
  have hB' : (fun u => B' u ω) = ⇑(V ω).B' := funext fun u => (h2.2.1 u).symm
  refine ⟨by rw [(hco ω).2.2.2.2.1]; exact h1.1, fun φ => ?_⟩
  rw [h1.2 φ, (hco ω).1, ← hB, ← hB']

/-- **The coupling data of the rescaled cone on the sample space of the environment.** For a valid
environment `S` with coupling data `V` and a level `b > 0` there is a measurable random element `V'`
of the data space, on the sample space of `S`, with the law of `V` and whose triple
`coneTriple γ V' = (h', η', β')` is almost surely the rescaled triple
`(h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` of `V`. Route: the rescaled triple is a Borel function of the
quadruple `(lateral part of X, (B, B'), η, β)`, hence independent of the uniform variable
`radialUniform X`, and it has the law of `coneTriple γ V`; the same-space lift does the rest. -/
theorem MatedCRTEnv.IsValid.exists_coneDataLift {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b) :
    ∃ V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData, Measurable V ∧
      MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V ∧ (∀ ω, (V ω).bm = S.bm ω) ∧
      (∀ᵐ ω ∂S.P, ⇑(V ω).η = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (V ω).X
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') φ) ∧
      Measurable V' ∧ S.P.map V' = S.P.map V ∧
      ∀ᵐ ω ∂S.P, MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ (V' ω) =
        coneRescaleOfQuad γ b (coneQuad (V ω)) := by
  obtain ⟨V, hV, hC, hbm, htie⟩ := hS.exists_couplingData_tied
  have hCP := (show MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _
    from hC)
  have := hCP.isProbabilityMeasure
  obtain ⟨hZm, hZlaw, hind⟩ := hS.radialUniform_coneData hγ hγ2 hV hC htie
  have hνP : IsProbabilityMeasure (S.P.map V) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 this
  have : Nonempty MatedCRTHarmonic.MatedCRT.CouplingData := (S.P.map V).nonempty_of_neZero
  have hY : Measurable fun ω => coneRescaleOfQuad γ b (coneQuad (V ω)) :=
    (measurable_coneRescaleOfQuad γ b).comp (measurable_coneQuad.comp hV)
  have hindY : IndepFun (fun ω => coneRescaleOfQuad γ b (coneQuad (V ω)))
      (fun ω => LatticeProb.LQG.radialUniform (V ω).X) S.P :=
    (hind.comp measurable_id (measurable_coneRescaleOfQuad γ b)).symm
  obtain ⟨V', hV', hlaw, hae⟩ := ProbabilityTheory.exists_map_eq_and_ae_comp_eq
    (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_coneTriple γ) hY
    (IsCouplingData.map_coneRescaleOfQuad hC hV hγ hγ2 hb) hZm hZlaw hindY
  exact ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩

end MatedCRT
