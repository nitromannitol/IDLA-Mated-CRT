import MatedCRT.FirstPass.S4S6c.CoverMinorantMeasurable
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# Lemma 2, eq (9): the dense minorant for an almost-everywhere random measure (q2, task fp-S4S6c; LEMMA68 gap G9)

The everywhere hypothesis `hκ` of `CoverMinorantMeasurable.goodAnnulusCover_dyadic_of_dense` is replaced by the freezable
almost-everywhere form: `μ` agrees almost surely with a `m'`-measurable random measure `g`. Then the dense cover of `g`
(`CoverMinorantMeasurable.denseCoverSet` with `g`) is `m'`-measurable, agrees with the dense cover of `μ` wherever
`μ ω = g ω`, and so
* is contained (a.s.) in the printed cover at radius `c₀` (`CoverMinorant.good_of_dense`);
* contains (a.s.) the `GoodAnnulusPrevalenceStmt` event at radius `c₀/2` (`CoverMinorant.dense_of_good`), hence has the same
  polynomial failure bound.
No countable union of null sets is needed: one full-measure set `{μ ω = g ω}` serves all scales, centres and radii.
`goodAnnulusCover_dyadic_of_frozen` specialises to a valid environment via the EXTERNAL `FrozenLQGMeasureFieldMeasurable`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace CoverMinorantAE

/-- The dense cover at a point depends only on the measure at that point. -/
theorem mem_denseCoverSet_congr {Ω : Type*} {μ g : Ω → Measure ℂ} {ω : Ω} (D : Set ℂ) (ρ c₀ C δ : ℝ)
    (h : μ ω = g ω) :
    ω ∈ CoverMinorantMeasurable.denseCoverSet D μ ρ c₀ C δ ↔ ω ∈ CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C δ := by
  simp only [CoverMinorantMeasurable.denseCoverSet, CoverMinorantMeasurable.denseGoodSet, Set.mem_ofPred_eq, h]

/-- **Lemma 2, eq (9), almost-everywhere form** (LEMMA68 Lemma 2 item 2). Given that `μ` agrees almost surely with an
`m'`-measurable random measure `g`, and the Draft polynomial bound at radius `c₀/2`, the dyadic good-radius conclusion holds on
an `m'`-measurable cutoff. -/
theorem goodAnnulusCover_dyadic_of_ae {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (hμm : ∃ g : Ω → Measure ℂ, Measurable[m'] g ∧ ∀ᵐ ω ∂P, μ ω = g ω)
    {D : Set ℂ} (hD : Dense D) (hDc : D.Countable) {ρ c₀ C : ℝ} (hc₀ : 0 < c₀)
    (hpoly : HarmonicBalls.PolyHighProb P (fun δ => GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C δ)) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ∀ z : ℂ,
        z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \
          Metric.ball (0 : ℂ) (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) →
        (∃ m k : ℤ, z = ((((1 / 2 : ℝ) ^ n) / 100 : ℝ) : ℂ) * (m + k * Complex.I)) →
        ∃ r : ℝ, (1 / 2 : ℝ) ^ n ≤ r ∧ r ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulusEvent (μ ω) c₀ C r z := by
  obtain ⟨g, hgm, hgae⟩ := hμm
  have hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(g ω) :=
    fun f hf => (Measure.measurable_lintegral hf).comp hgm
  have hFm : ∀ n : ℕ, MeasurableSet[m']
      (CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C ((1 / 2 : ℝ) ^ n)) :=
    fun n => CoverMinorantMeasurable.measurableSet_denseCoverSet g hκ hDc _ _ _ _
  -- deterministic inclusions, pointwise in `ω`
  have hsubE : ∀ n : ℕ, GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n) ⊆
      CoverMinorantMeasurable.denseCoverSet D μ ρ c₀ C ((1 / 2 : ℝ) ^ n) := by
    intro n ω hω z hz hzg
    obtain ⟨r, h1, h2, h3, hG⟩ := hω z hz hzg
    exact ⟨r, h1, h2, h3, CoverMinorant.dense_of_good (D := D) (μ ω) hG⟩
  have hsubC : ∀ n : ℕ, CoverMinorantMeasurable.denseCoverSet D μ ρ c₀ C ((1 / 2 : ℝ) ^ n) ⊆
      GoodRadiusCover.GoodAnnulusCoverEvent μ ρ c₀ C ((1 / 2 : ℝ) ^ n) := by
    intro n ω hω z hz hzg
    obtain ⟨r, h1, h2, h3, hG⟩ := hω z hz hzg
    have hr : 0 < r := lt_of_lt_of_le (by positivity) h1
    exact ⟨r, h1, h2, h3, CoverMinorant.good_of_dense hD hr hc₀ (μ ω) hG⟩
  -- the summability of the complements: they are contained in those of the Draft event, up to the null set `{μ ≠ g}`
  have hsum : ∑' n : ℕ, P (CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C ((1 / 2 : ℝ) ^ n))ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ConstantOrderDiv.tsum_dyadic_ne_top hpoly) (ENNReal.tsum_le_tsum fun n => ?_)
    have hsub : (CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C ((1 / 2 : ℝ) ^ n))ᶜ ⊆
        (GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n))ᶜ ∪ {ω | ¬ μ ω = g ω} := by
      intro ω hω
      by_cases hG : μ ω = g ω
      · left
        intro hE
        exact hω ((mem_denseCoverSet_congr D ρ c₀ C _ hG).1 (hsubE n hE))
      · right
        exact hG
    calc P (CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C ((1 / 2 : ℝ) ^ n))ᶜ
        ≤ P ((GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n))ᶜ ∪ {ω | ¬ μ ω = g ω}) :=
          measure_mono hsub
      _ ≤ P (GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n))ᶜ +
            P {ω | ¬ μ ω = g ω} := measure_union_le _ _
      _ = P (GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n))ᶜ := by
          rw [ae_iff.1 hgae, add_zero]
  obtain ⟨N, hNm, hN⟩ := ConstantOrderDiv.exists_measurable_threshold P hFm hsum
  have hpow : Measurable[m'] fun ω => (1 / 2 : ℝ) ^ N ω :=
    (measurable_from_nat (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)).comp hNm
  refine ⟨fun ω => (1 / 2 : ℝ) ^ N ω, hpow, ?_⟩
  filter_upwards [hN, hgae] with ω hω hμω
  refine ⟨by positivity, fun n hn z hz hzg => ?_⟩
  have hFn : ω ∈ CoverMinorantMeasurable.denseCoverSet D g ρ c₀ C ((1 / 2 : ℝ) ^ n) := by
    apply hω n
    by_contra h
    have hlt : n < N ω := not_le.1 h
    have hle : (1 / 2 : ℝ) ^ N ω ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
    linarith
  exact hsubC n ((mem_denseCoverSet_congr D ρ c₀ C _ hμω).2 hFn) z hz hzg

/-- **Lemma 2, eq (9), for a valid environment**: the almost-everywhere measurability of the LQG measure (EXTERNAL,
`FrozenLQGMeasureFieldMeasurable`) gives the dyadic good-radius conclusion with a `σ(h)`-measurable cutoff. -/
theorem goodAnnulusCover_dyadic_of_frozen {𝒮 : SpaceFillingSLEModel}
    (hfr : FrozenLQGMeasureFieldMeasurable 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {D : Set ℂ} (hD : Dense D) (hDc : D.Countable) {ρ c₀ C : ℝ} (hc₀ : 0 < c₀)
    (hpoly : HarmonicBalls.PolyHighProb S.P (fun δ => GoodRadiusCover.GoodAnnulusCoverEvent S.μ ρ (c₀ / 2) C δ)) :
    ∃ tStar : Ω → ℝ, Measurable[S.fieldSigma] tStar ∧ ∀ᵐ ω ∂S.P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ∀ z : ℂ,
        z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \
          Metric.ball (0 : ℂ) (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) →
        (∃ m k : ℤ, z = ((((1 / 2 : ℝ) ^ n) / 100 : ℝ) : ℂ) * (m + k * Complex.I)) →
        ∃ r : ℝ, (1 / 2 : ℝ) ^ n ≤ r ∧ r ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulusEvent (S.μ ω) c₀ C r z := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact goodAnnulusCover_dyadic_of_ae S.μ (hfr γ hγ hγ2 Ω S hS) hD hDc hc₀ hpoly

/-- **Lemma 2, eq (9), first-pass form on a valid environment.** The Draft prevalence statement `GoodAnnulusPrevalenceStmt`
(Draft/Section6.lean:60) at radius `c₀ / 2` gives the constant `C` and the polynomial bound for a cone field; a valid environment
is a cone field (`IsValid` supplies the probability, quantum-cone and LQG-measure conjuncts of `IsConeField`); the frozen
a.e. measurability `FrozenLQGMeasureFieldMeasurable` then gives the dyadic good-radius cover with a `σ(h)`-measurable cutoff. -/
theorem goodAnnulusCover_dyadic_firstPass {𝒮 : SpaceFillingSLEModel}
    (hprev : GoodAnnulusPrevalenceStmt) (hfr : FrozenLQGMeasureFieldMeasurable 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 2 / 5)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {D : Set ℂ} (hD : Dense D) (hDc : D.Countable) :
    ∃ C : ℝ, 0 < C ∧ ∃ tStar : Ω → ℝ, Measurable[S.fieldSigma] tStar ∧ ∀ᵐ ω ∂S.P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ∀ z : ℂ,
        z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \
          Metric.ball (0 : ℂ) (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) →
        (∃ m k : ℤ, z = ((((1 / 2 : ℝ) ^ n) / 100 : ℝ) : ℂ) * (m + k * Complex.I)) →
        ∃ r : ℝ, (1 / 2 : ℝ) ^ n ≤ r ∧ r ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulusEvent (S.μ ω) c₀ C r z := by
  obtain ⟨C, hC0, hpolyAll⟩ := GoodRadiusCover.cover_polyHighProb_of_prevalence hprev hγ hγ2 hρ hρ1
    (half_pos hc₀) (by linarith)
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  exact ⟨C, hC0, goodAnnulusCover_dyadic_of_frozen hfr hγ hγ2 S hS hD hDc hc₀
    (hpolyAll Ω S.P S.hC S.hcirc S.μ hcone)⟩

#print axioms MatedCRT.CoverMinorantAE.goodAnnulusCover_dyadic_of_ae
#print axioms MatedCRT.CoverMinorantAE.goodAnnulusCover_dyadic_of_frozen

end CoverMinorantAE

end MatedCRT

#print axioms MatedCRT.CoverMinorantAE.goodAnnulusCover_dyadic_firstPass
