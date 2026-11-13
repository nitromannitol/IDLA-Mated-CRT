import MatedCRT.FirstPass.Derived.ConeScaleRadiusPair
import MatedCRT.FirstPass.Derived.ConeBoundaryLengthScale

/-!
# The rescaled cone data of the lift, read off the environment

Let `S` be a valid environment with coupling data `V` tied to `S` (its curve is the curve of `S`
and its cone field has the pairings of the field of `S`), and let `V'` be a random element of the
data space whose triple is almost surely the rescaled triple of `V`
(`MatedCRTEnv.IsValid.exists_coneDataLift`). Then almost surely:

* the curve of `V'` is `R_b⁻¹ η(b ·)`, for the curve `η` of `S` and the cone scale radius
  `R_b = coneScaleRadius γ h b` of the circle-average process of `S`;
* the boundary-length pair of `V'` is the Brownian rescaling `rescaledPair b` of that of `S`;
* the cone field of `V'` has the pairings `rescaledPairing γ h R_b b` of the field
  `h(R_b ·) + Q log R_b - γ⁻¹ log b` of `S`.

These are the identities of the rescaled γ-quantum cone (Duplantier-Miller-Sheffield, Prop. 4.13(i);
paper, eq:quantum-cone-scaling) on the sample space of `S`: the scale `R_b` read off the radial paths
of the data is the scale read off the circle averages of `S`
(`MatedCRTEnv.IsValid.ae_coneScaleRadius_eq_coneScaleOfPair`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace MatedCRT

/-- The pairings `rescaledPairing γ g R b` of a field `g` against test functions are the pairings of
the distribution `coneRescaleField γ R b F = F(R ·) + Q log R - γ⁻¹ log b` whenever `g` and `F` have
the same pairings and `R ≠ 0` (change of variables `y = R x`). -/
theorem rescaledPairing_eq_coneRescaleField {γ R b : ℝ} (hR : R ≠ 0) {g : (ℂ → ℝ) → ℝ}
    {F : MatedCRTHarmonic.MatedCRT.Field} (hg : ∀ φ : LQGMetric.TestC, g ⇑φ = F φ)
    (φ : LQGMetric.TestC) :
    rescaledPairing γ g R b ⇑φ = MatedCRTHarmonic.MatedCRT.coneRescaleField γ R b F φ := by
  have hpull : (fun x : ℂ => φ ((R⁻¹ : ℂ) * x)) = ⇑(LQGMetric.testAffinePull R 0 φ) := by
    funext x
    rw [LQGMetric.testAffinePull_apply R 0 hR, sub_zero, div_eq_inv_mul]
  have hQ : _root_.HarmonicBalls.lqgQ γ = MatedCRTHarmonic.MatedCRT.lqgQ γ := rfl
  simp only [rescaledPairing, MatedCRTHarmonic.MatedCRT.coneRescaleField,
    LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.affineComp_apply, hpull, hg, inv_pow, hQ]
  ring

/-- **The rescaled cone data of the lift.** For a valid environment `S`, coupling data `V` tied to
`S`, and a measurable `V'` with the law of `V` whose triple is almost surely the rescaled triple of
`V`, almost surely the curve of `V'` is `R_b⁻¹ η(b ·)`, its boundary-length pair is
`rescaledPair b` of that of `S`, and its cone field has the pairings `rescaledPairing γ h R_b b`,
where `R_b = coneScaleRadius γ h b` is read off the circle averages of `S`. -/
theorem MatedCRTEnv.IsValid.ae_coneDataLift_rescaled {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b) {V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hV : Measurable V) (hC : MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V)
    (hbm : ∀ ω, (V ω).bm = S.bm ω)
    (htie : ∀ᵐ ω ∂S.P, ⇑(V ω).η = S.η ω ∧ ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (V ω).X
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') φ)
    (hV' : Measurable V') (hlaw : S.P.map V' = S.P.map V)
    (hae : ∀ᵐ ω ∂S.P, MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ (V' ω) =
      coneRescaleOfQuad γ b (coneQuad (V ω))) :
    ∀ᵐ ω ∂S.P,
      ⇑(V' ω).η = (fun s => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
      (V' ω).bm = rescaledPair b (S.bm ω) ∧
      ∀ φ : LQGMetric.TestC,
        rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b ⇑φ =
          MatedCRTHarmonic.MatedCRT.coneField (V' ω).X
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V' ω).B (V' ω).B') φ := by
  have hs : MeasurableSet {v : MatedCRTHarmonic.MatedCRT.CouplingData |
      (v.B, v.B') ∈ MatedCRTHarmonic.ConeScaling.radGood γ γ} :=
    (MatedCRTHarmonic.ConeScaling.measurableSet_radGood γ γ).preimage
      (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_B.prodMk
        MatedCRTHarmonic.MatedCRT.CouplingData.measurable_B')
  have hgood' : ∀ᵐ ω ∂S.P, ((V' ω).B, (V' ω).B') ∈ MatedCRTHarmonic.ConeScaling.radGood γ γ := by
    have h1 : ∀ᵐ v ∂S.P.map V, (v.B, v.B') ∈ MatedCRTHarmonic.ConeScaling.radGood γ γ :=
      (ae_map_iff hV.aemeasurable hs).2 (hC.ae_radGood hγ hγ2)
    rw [← hlaw] at h1
    exact (ae_map_iff hV'.aemeasurable hs).1 h1
  filter_upwards [htie, hae, hS.ae_coneScaleRadius_eq_coneScaleOfPair hγ hγ2 hC
      (htie.mono fun _ h => h.2) b, hC.ae_radGood hγ hγ2, hgood'] with ω ht ha hR hg hg'
  have hRpos : 0 < coneScaleOfPair γ b ((V ω).B, (V ω).B') := Real.exp_pos _
  have h2 : (V' ω).η = MatedCRTHarmonic.MatedCRT.coneRescaleCurve
      (coneScaleOfPair γ b ((V ω).B, (V ω).B')) b (V ω).η := congrArg (fun p => p.2.1) ha
  have h3 : (V' ω).bm = MatedCRTHarmonic.MatedCRT.brownRescale b (V ω).bm :=
    congrArg (fun p => p.2.2) ha
  have h1 : MatedCRTHarmonic.MatedCRT.coneField (V' ω).X
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V' ω).B (V' ω).B') =
      MatedCRTHarmonic.MatedCRT.coneRescaleField γ (coneScaleOfPair γ b ((V ω).B, (V ω).B')) b
        (MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ (V ω)).1 := by
    rw [← MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple_fst_of_mem hg']
    exact congrArg Prod.fst ha
  rw [MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple_fst_of_mem hg] at h1
  refine ⟨?_, by rw [h3, hbm, Sec1.brownRescale_eq_rescaledPair hb], fun φ => ?_⟩
  · rw [h2, hR, ← ht.1]
    funext s
    simp only [MatedCRTHarmonic.MatedCRT.coneRescaleCurve, ContinuousMap.coe_mk, Complex.ofReal_inv]
  · rw [h1, hR]
    exact rescaledPairing_eq_coneRescaleField hRpos.ne' ht.2 φ

/-- **Assembly of the rescaled mating-of-trees representation from the lift.** If the lift `V'` is
coupling data (a mating-of-trees coupling on the sample space of `S`) and almost surely its curve,
boundary-length pair and cone-field pairings are those of the rescaled environment
(`MatedCRTEnv.IsValid.ae_coneDataLift_rescaled`), then for every `hC'` with almost surely the
pairings `rescaledPairing γ h R_b b` on test functions, the coordinates of `V'` give the
mating-of-trees coupling of the rescaled environment with boundary-length pair exactly
`rescaledPair b` of that of `S`, whose curve is almost surely `R_b⁻¹ η(b ·)` and whose cone field
almost surely has the pairings of `hC'`. -/
theorem MatedCRTEnv.rescaledMatingOfTrees_of_lift {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {γ b : ℝ} (hb : 0 < b) {V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hV : Measurable V) (hbm : ∀ ω, (V ω).bm = S.bm ω)
    (hC' : MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V')
    (hid : ∀ᵐ ω ∂S.P,
      ⇑(V' ω).η = (fun s => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
      (V' ω).bm = rescaledPair b (S.bm ω) ∧
      ∀ φ : LQGMetric.TestC,
        rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b ⇑φ =
          MatedCRTHarmonic.MatedCRT.coneField (V' ω).X
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V' ω).B (V' ω).B') φ)
    {hC'' : Ω → (ℂ → ℝ) → ℝ}
    (hpair : ∀ᵐ ω ∂S.P, ∀ φ, _root_.HarmonicBalls.IsTestFunction Set.univ φ →
      hC'' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
          (fun ω => rescaledPair b (S.bm ω)) ∧
      ∀ᵐ ω ∂S.P, ⇑(η' ω) = (fun s => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
        ∀ φ : LQGMetric.TestC, hC'' ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
  have hm : Measurable fun ω => rescaledPair b (S.bm ω) := by
    have he : (fun ω => rescaledPair b (S.bm ω)) =
        fun ω => MatedCRTHarmonic.MatedCRT.brownRescale b (V ω).bm :=
      funext fun ω => by rw [hbm, Sec1.brownRescale_eq_rescaledPair hb]
    rw [he]
    exact (MatedCRTHarmonic.MatedCRT.measurable_brownRescale b).comp
      (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm.comp hV)
  refine ⟨fun ω => (V' ω).X, fun ω => (V' ω).X₀, fun ω => (V' ω).hIG, fun t ω => (V' ω).B t,
    fun t ω => (V' ω).B' t, fun t ω => (V' ω).B₀ t, fun t ω => (V' ω).B₀' t, fun ω => (V' ω).U,
    fun ω => (V' ω).ηL, fun ω => (V' ω).η, fun ω => (V' ω).η₀,
    MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling.congr_bm
      (show MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC')
      hm (hid.mono fun _ h => h.2.1.symm), ?_⟩
  filter_upwards [hid, hpair] with ω h h'
  exact ⟨h.1, fun φ => (h' φ ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩).trans (h.2.2 φ)⟩

end MatedCRT
