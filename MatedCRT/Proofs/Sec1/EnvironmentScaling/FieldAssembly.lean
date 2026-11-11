import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proposed.DuplantierMillerSheffieldCone2014

/-!
# Distributional cone scaling through the canonical law

The canonical identification remains a separate
obligation.  Given the joint law of the distribution and its embedding radius,
the DMS scaling law transfers to the environment's representative.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal
open HarmonicBalls

namespace MatedCRT.Sec1

/-- A countable test for absence of a circle-average level above `q`. -/
private def distributionRadiusTest (γ b : ℝ) (H : LQGMetric.DistC) (q : ℚ) : Prop :=
  ∀ M : ℕ, ∃ k : ℕ, ∀ x : {x : ℚ // (q : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ M},
    1 / ((k : ℝ) + 1) ≤
      |distributionCircleVersion H x 0 + lqgQ γ * Real.log x - γ⁻¹ * Real.log b|

/-- Borel reconstruction of the embedding radius from the distribution.
The value outside the continuous positive-radius event is a harmless default. -/
def distributionEmbeddingRadius (γ b : ℝ) (H : LQGMetric.DistC) : ℝ := by
  classical
  exact (⨅ q : ℚ, if 0 < (q : ℝ) ∧ distributionRadiusTest γ b H q
    then ENNReal.ofReal q else ⊤).toReal

theorem measurable_distributionEmbeddingRadius (γ b : ℝ) :
    Measurable (distributionEmbeddingRadius γ b) := by
  classical
  have ht : ∀ q : ℚ, MeasurableSet {H | distributionRadiusTest γ b H q} := by
    intro q
    simp only [distributionRadiusTest, Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun k =>
      MeasurableSet.iInter fun x => ?_
    exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp
        (((measurable_distributionCircleVersion_fixed x 0).add_const _).sub_const _))
  unfold distributionEmbeddingRadius
  exact (Measurable.iInf fun q =>
    Measurable.ite ((MeasurableSet.const _).inter (ht q)) measurable_const measurable_const).ennreal_toReal

/-- If the recovered circles agree with a continuous circle process whose
level radius is positive, the Borel reconstruction gives that radius exactly. -/
theorem distributionEmbeddingRadius_eq (γ b : ℝ) (H : LQGMetric.DistC)
    (a : ℝ → ℂ → ℝ)
    (hc : ContinuousOn (fun r : ℝ => a r 0) (Ioi 0))
    (heq : ∀ r, 0 < r → distributionCircleVersion H r 0 = a r 0)
    (hpos : 0 < coneScaleRadius γ a b) :
    distributionEmbeddingRadius γ b H = coneScaleRadius γ a b := by
  classical
  let X : ℝ → ℝ := fun r => a r 0 + lqgQ γ * Real.log r
  let c : ℝ := γ⁻¹ * Real.log b
  have hX : ContinuousOn X (Ioi 0) :=
    hc.add (continuousOn_const.mul (Real.continuousOn_log.mono fun r hr => hr.ne'))
  have ht : ∀ q : ℚ, 0 < (q : ℝ) →
      (distributionRadiusTest γ b H q ↔ coneScaleRadius γ a b < q) := by
    intro q hq
    have htest : distributionRadiusTest γ b H q ↔ ∀ M : ℕ, ∃ k : ℕ,
        ∀ x : {x : ℚ // (q : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ M},
          1 / ((k : ℝ) + 1) ≤ |X x - c| := by
      unfold distributionRadiusTest
      apply forall_congr' fun M => exists_congr fun k => forall_congr' fun x => ?_
      rw [heq x (lt_of_lt_of_le hq x.2.1)]
    rw [htest]
    exact (sSup_levelSet_lt_iff hX hpos hq).symm
  let F : ℚ → ℝ≥0∞ := fun q =>
    if 0 < (q : ℝ) ∧ distributionRadiusTest γ b H q then ENNReal.ofReal q else ⊤
  obtain ⟨q₀, hq₀, _⟩ := exists_rat_btwn
    (show coneScaleRadius γ a b < coneScaleRadius γ a b + 1 by linarith)
  have hq₀pos : 0 < (q₀ : ℝ) := hpos.trans hq₀
  have hF₀ : F q₀ = ENNReal.ofReal q₀ := by
    dsimp only [F]
    rw [ite_eq_left ⟨hq₀pos, (ht q₀ hq₀pos).2 hq₀⟩]
  have hfinite : (⨅ q : ℚ, F q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by simpa only [hF₀] using iInf_le F q₀)
  have hlower : ENNReal.ofReal (coneScaleRadius γ a b) ≤ ⨅ q : ℚ, F q := by
    refine le_iInf fun q => ?_
    by_cases hq : 0 < (q : ℝ) ∧ distributionRadiusTest γ b H q
    · dsimp only [F]
      rw [ite_eq_left hq]
      exact ENNReal.ofReal_le_ofReal ((ht q hq.1).1 hq.2).le
    · dsimp only [F]
      rw [ite_eq_right hq]
      exact le_top
  have hlower' : coneScaleRadius γ a b ≤ distributionEmbeddingRadius γ b H := by
    have h := ENNReal.toReal_mono hfinite hlower
    simpa [distributionEmbeddingRadius, F, ENNReal.toReal_ofReal hpos.le] using h
  have hupper : distributionEmbeddingRadius γ b H ≤ coneScaleRadius γ a b := by
    apply le_of_forall_gt
    intro v hv
    obtain ⟨q, hq, hqv⟩ := exists_rat_btwn hv
    have hqpos : 0 < (q : ℝ) := hpos.trans hq
    have hFq : F q = ENNReal.ofReal q := by
      dsimp only [F]
      rw [ite_eq_left ⟨hqpos, (ht q hqpos).2 hq⟩]
    have hle : (⨅ q : ℚ, F q) ≤ ENNReal.ofReal q := by
      simpa only [hFq] using iInf_le F q
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    have h' : distributionEmbeddingRadius γ b H ≤ (q : ℝ) := by
      simpa [distributionEmbeddingRadius, F, ENNReal.toReal_ofReal hqpos.le] using h
    exact h'.trans_lt hqv
  exact le_antisymm hupper hlower'

/-- The embedding radius of a represented cone is recovered from its
distribution on one event. -/
theorem ae_distributionEmbeddingRadius_eq
    (hscale : QuantumConeScalingInput) {γ b : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {H : Ω → LQGMetric.DistC}
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, distributionEmbeddingRadius γ b (H ω) = coneScaleRadius γ (S.hcirc ω) b := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  filter_upwards [ae_distributionCircleVersion_eq hS hrep,
    hS.isQuantumCone.ae_continuousOn_circle,
    ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb] with ω heq hc hp
  apply distributionEmbeddingRadius_eq γ b (H ω) (S.hcirc ω) ?_ (fun r hr => heq r hr 0) hp
  exact hc.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun r hr => ⟨hr, mem_univ _⟩)

/-- Equal distribution laws give equal joint field–radius laws when the
reference radius is the same recovered Borel function of its field. -/
theorem map_distribution_radius_eq_of_distribution_law
    (hscale : QuantumConeScalingInput) {γ b : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {𝒮 : SpaceFillingSLEModel} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {P' : Measure Ω'} {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    {R : Ω → ℝ} {R' : Ω' → ℝ} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hR : ∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b)
    (hR' : ∀ᵐ ω ∂P', R' ω = distributionEmbeddingRadius γ b (H' ω))
    (hlaw : S.P.map H = P'.map H') :
    S.P.map (fun ω => (H ω, R ω)) = P'.map (fun ω => (H' ω, R' ω)) := by
  have hleft : (fun ω => (H ω, R ω)) =ᵐ[S.P]
      (fun ω => (H ω, distributionEmbeddingRadius γ b (H ω))) := by
    filter_upwards [hR, ae_distributionEmbeddingRadius_eq hscale hγ hγ2 hb hS hrep] with ω hr hd
    rw [hr, hd]
  have hright : (fun ω => (H' ω, R' ω)) =ᵐ[P']
      (fun ω => (H' ω, distributionEmbeddingRadius γ b (H' ω))) := by
    filter_upwards [hR'] with ω hr
    rw [hr]
  have hf : Measurable (fun d : LQGMetric.DistC => (d, distributionEmbeddingRadius γ b d)) :=
    measurable_id.prodMk (measurable_distributionEmbeddingRadius γ b)
  rw [Measure.map_congr hleft, Measure.map_congr hright]
  change S.P.map ((fun d => (d, distributionEmbeddingRadius γ b d)) ∘ H) =
    P'.map ((fun d => (d, distributionEmbeddingRadius γ b d)) ∘ H')
  rw [← Measure.map_map hf hH, ← Measure.map_map hf hH', hlaw]

/-- The remaining canonical field-law identification and reference-radius
recovery, before forming any joint law. This is an internal proof obligation. -/
def CanonicalConeDistributionLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ H : Ω → LQGMetric.DistC, Measurable H →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (X : Ω' → LQGMetric.DistC) (B B' : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' ∧
        LQGMetric.IsWholePlaneGFF X P' ∧ IsBrownianReal B P' ∧ IsBrownianReal B' P' ∧
        IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P' ∧
        IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P' ∧
        let H' : Ω' → LQGMetric.DistC := fun ω =>
          MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
        Measurable H' ∧ S.P.map H = P'.map H' ∧
        ∀ᵐ ω ∂P', Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
          (fun t => B t ω) (fun t => B' t ω) = distributionEmbeddingRadius γ b (H' ω)

/-- The canonical joint distribution and embedding-radius identification.
This is the remaining internal identification,
not a literature input or the conclusion of the scaling theorem. -/
def CanonicalConeDistributionRadiusLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (X : Ω' → LQGMetric.DistC) (B B' : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' ∧
        LQGMetric.IsWholePlaneGFF X P' ∧ IsBrownianReal B P' ∧ IsBrownianReal B' P' ∧
        IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P' ∧
        IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P' ∧
        AEMeasurable (fun ω =>
          (MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
           Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
            (fun t => B t ω) (fun t => B' t ω))) P' ∧
        S.P.map (fun ω => (H ω, R ω)) = P'.map (fun ω =>
          (MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
           Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
            (fun t => B t ω) (fun t => B' t ω)))

/-- Canonical field law and reference radius recovery imply the canonical
joint field–radius law. -/
theorem canonicalConeDistributionRadiusLawStep_of_distribution
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcanonical : CanonicalConeDistributionLawStep 𝒮) :
    CanonicalConeDistributionRadiusLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hHm _ hrep hR
  obtain ⟨Ω', mΩ', P', X, B, B', hprob, hX, hB, hB', hind, hindB, hH', hlaw, hR'⟩ :=
    hcanonical γ hγ hγ2 Ω S hS b hb H hHm hrep
  let : MeasurableSpace Ω' := mΩ'
  let H' : Ω' → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  let R' : Ω' → ℝ := fun ω => Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
    (fun t => B t ω) (fun t => B' t ω)
  have hjoint := map_distribution_radius_eq_of_distribution_law hscale hγ hγ2 hb hS
    hHm hH' hrep hR hR' hlaw
  have hR'' : (fun ω => distributionEmbeddingRadius γ b (H' ω)) =ᵐ[P'] R' := by
    filter_upwards [hR'] with ω hr
    exact hr.symm
  have hmR' : AEMeasurable R' P' :=
    ((measurable_distributionEmbeddingRadius γ b).comp hH').aemeasurable.congr hR''
  exact ⟨Ω', mΩ', P', X, B, B', hprob, hX, hB, hB', hind, hindB,
    hH'.aemeasurable.prodMk hmR', hjoint⟩

/-- DMS scaling transfers through the joint field–radius law; the latter is
still to be proved from the canonical cone identification. -/
theorem rescaledConeDistributionLawStep_of_canonical
    (𝒮 : SpaceFillingSLEModel) (hdms : Proposed.DMS14ConeScaling)
    (hcanonical : CanonicalConeDistributionRadiusLawStep 𝒮) :
    RescaledConeDistributionLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hHm hRm hrep hR
  obtain ⟨Ω', mΩ', P', X, B, B', hprob, hX, hB, hB', hind, hindB, hmeas, hjoint⟩ :=
    hcanonical γ hγ hγ2 Ω S hS b hb H R hHm hRm hrep hR
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hprob
  let H' : Ω' → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  let R' : Ω' → ℝ := fun ω => Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
    (fun t => B t ω) (fun t => B' t ω)
  have hq : γ < MatedCRTHarmonic.MatedCRT.lqgQ γ := by
    unfold MatedCRTHarmonic.MatedCRT.lqgQ
    have hsq : γ * γ < 4 := by nlinarith
    have hhalf : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hγ]
      nlinarith
    linarith
  have hscale := hdms γ γ hγ hγ2 hq Ω' P' X B B' hX hB hB' hind hindB (-Real.log b)
  have hscale' : P'.map (fun ω => rescaledDistribution γ b (H' ω) (R' ω)) = P'.map H' := by
    convert hscale using 1
    congr 1
    funext ω
    simp only [rescaledDistribution, H', R', HarmonicBalls.lqgQ,
      MatedCRTHarmonic.MatedCRT.lqgQ, div_eq_mul_inv]
    congr 1
    ring
  have hpair : Measurable (fun ω => (H ω, R ω)) := hHm.prodMk hRm
  calc
    S.P.map (fun ω => rescaledDistribution γ b (H ω) (R ω)) =
        (S.P.map (fun ω => (H ω, R ω))).map
          (fun p => rescaledDistribution γ b p.1 p.2) :=
      (Measure.map_map (measurable_rescaledDistribution γ b) hpair).symm
    _ = (P'.map (fun ω => (H' ω, R' ω))).map
          (fun p => rescaledDistribution γ b p.1 p.2) := by rw [hjoint]
    _ = P'.map (fun ω => rescaledDistribution γ b (H' ω) (R' ω)) :=
      AEMeasurable.map_map_of_aemeasurable (measurable_rescaledDistribution γ b).aemeasurable hmeas
    _ = P'.map H' := hscale'
    _ = (P'.map (fun ω => (H' ω, R' ω))).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hmeas).symm
    _ = (S.P.map (fun ω => (H ω, R ω))).map Prod.fst := by rw [hjoint]
    _ = S.P.map H := Measure.map_map measurable_fst hpair

/-- Conditional field assembly.  The canonical joint law and the fixed-grid
circle identities remain independent proof obligations. -/
theorem rescaledConeFieldStep_of_canonical_and_grid
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hdms : Proposed.DMS14ConeScaling)
    (hcanonical : CanonicalConeDistributionRadiusLawStep 𝒮)
    (hgrid : RescaledConeDistributionCircleGridStep 𝒮) :
    RescaledConeFieldStep 𝒮 := by
  apply rescaledConeFieldStep_of_observable_law 𝒮 hscale
  apply rescaledConeObservableLawStep_of_represented_law 𝒮
  apply rescaledConeRepresentedLawStep_of_distribution 𝒮 hscale
  · exact rescaledConeDistributionCircleStep_of_grid 𝒮 hscale hgrid
  · exact rescaledConeDistributionLawStep_of_canonical 𝒮 hdms hcanonical

/-- Conditional field assembly using canonical field-law identification and
reference-radius recovery rather than assuming their joint law. -/
theorem rescaledConeFieldStep_of_distribution_and_grid
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hdms : Proposed.DMS14ConeScaling)
    (hcanonical : CanonicalConeDistributionLawStep 𝒮)
    (hgrid : RescaledConeDistributionCircleGridStep 𝒮) :
    RescaledConeFieldStep 𝒮 :=
  rescaledConeFieldStep_of_canonical_and_grid 𝒮 hscale hdms
    (canonicalConeDistributionRadiusLawStep_of_distribution 𝒮 hscale hcanonical) hgrid

end MatedCRT.Sec1
