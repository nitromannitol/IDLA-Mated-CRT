import MatedCRT.FirstPass.S4S6c.CoverMinorant
import MatedCRT.FirstPass.S4S6c.GoodRadiusCover

/-!
# Lemma 2, eq (9): field-measurability of the dense good-annulus minorant (q2, task fp-S4S6c; LEMMA68 gap G9)

The dense cover `denseCoverSet` at scale `δ` is the grid form of `GoodAnnulusCoverEvent` (GoodRadiusCover.lean) with the
supremum and infimum of `IsGoodAnnulusEvent` replaced by suprema and infima over a countable dense set `D ∩ 𝔸` (CoverMinorant.lean).
* `CoverMinorant.good_of_dense`: the dense cover at radius `c₀` implies the printed cover at radius `c₀`.
* `CoverMinorant.dense_of_good`: the printed cover at radius `c₀ / 2` (the `GoodAnnulusPrevalenceStmt` event) implies the dense
  cover at radius `c₀`. So the dense cover is a minorant with the polynomial failure bound of the Draft event.
* Measurability: the random measure hypothesis `hκ` (`ω ↦ ∫⁻ f dμ_ω` is measurable for measurable `f ≥ 0`) gives
  measurability of ball masses and log potentials; countable suprema and infima and the grid index `(m, k) ∈ ℤ²` give
  measurability of `denseCoverSet`. WARNING: `hκ` is stated EVERYWHERE, which is NOT a freezable form: `IsLQGMeasure` holds
  only almost surely (Harmonic-Balls-LQG HarmonicBalls/Defs/LQG.lean:63-65), so `S.μ` can be altered on a null set. The
  freezable form is a.e.: for each measurable `f ≥ 0` a fieldSigma-measurable `g` with `g = ∫⁻ f dμ_ω` a.s.; the minorant
  then needs null-set bookkeeping over the countable families used. OPEN; this file is conditional on the everywhere form.
* `goodAnnulusCover_dyadic_of_dense`: the dyadic good-radius conclusion (eq (9)) from `hκ`, the countability of `D`, and the
  Draft polynomial bound at radius `c₀ / 2`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace CoverMinorantMeasurable

/-- The dense good-annulus event at centre `z`, radius `r`, cover constant `c₀`, constant `C`: the supremum over the countable
dense set `D ∩ 𝔸_{r,2r}(z)` of the log potential is at most `C` times the infimum over that set of the ball masses of radius
`c₀ r / 2`. -/
def denseGoodSet {Ω : Type*} (D : Set ℂ) (μ : Ω → Measure ℂ) (c₀ C r : ℝ) (z : ℂ) : Set Ω :=
  {ω | (⨆ d ∈ D ∩ HarmonicBalls.annulus z r (2 * r),
        ∫⁻ u in HarmonicBalls.annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂(μ ω)) ≤
      ENNReal.ofReal C * ⨅ q ∈ D ∩ HarmonicBalls.annulus z r (2 * r), μ ω (Metric.ball q (c₀ / 2 * r))}

/-- The dense cover event at scale `δ`: the grid form of `GoodAnnulusCoverEvent` with `denseGoodSet` in place of
`IsGoodAnnulusEvent`. -/
def denseCoverSet {Ω : Type*} (D : Set ℂ) (μ : Ω → Measure ℂ) (ρ c₀ C δ : ℝ) : Set Ω :=
  {ω | ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt δ) \ Metric.ball (0 : ℂ) (10 * Real.sqrt δ) →
    (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
    ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ ω ∈ denseGoodSet D μ c₀ C r z}

section Measurability

variable {Ω : Type*} {m' : MeasurableSpace Ω}

theorem measurable_lintegral_set (μ : Ω → Measure ℂ)
    (hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(μ ω))
    {A : Set ℂ} (hA : MeasurableSet A) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable[m'] fun ω => ∫⁻ u in A, g u ∂(μ ω) := by
  have h : (fun ω => ∫⁻ u in A, g u ∂(μ ω)) = fun ω => ∫⁻ u, A.indicator g u ∂(μ ω) :=
    funext fun ω => by rw [lintegral_indicator hA]
  rw [h]
  exact hκ _ (hg.indicator hA)

theorem measurable_measure_set (μ : Ω → Measure ℂ)
    (hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(μ ω))
    {s : Set ℂ} (hs : MeasurableSet s) : Measurable[m'] fun ω => μ ω s := by
  have h : (fun ω => μ ω s) = fun ω => ∫⁻ u, s.indicator 1 u ∂(μ ω) :=
    funext fun ω => by rw [lintegral_indicator_one hs]
  rw [h]
  exact hκ _ (Measurable.indicator measurable_const hs)

theorem measurable_iSup_dense {S : Set ℂ} (hS : S.Countable) (F : ℂ → Ω → ℝ≥0∞)
    (hF : ∀ d, Measurable[m'] (F d)) : Measurable[m'] fun ω => ⨆ d ∈ S, F d ω := by
  have : Countable ↥S := hS.to_subtype
  have h : (fun ω => ⨆ d ∈ S, F d ω) = fun ω => ⨆ d : ↥S, F d.1 ω :=
    funext fun ω => by rw [iSup_subtype']
  rw [h]
  exact Measurable.iSup fun d => hF d.1

theorem measurable_iInf_dense {S : Set ℂ} (hS : S.Countable) (F : ℂ → Ω → ℝ≥0∞)
    (hF : ∀ d, Measurable[m'] (F d)) : Measurable[m'] fun ω => ⨅ d ∈ S, F d ω := by
  have : Countable ↥S := hS.to_subtype
  have h : (fun ω => ⨅ d ∈ S, F d ω) = fun ω => ⨅ d : ↥S, F d.1 ω :=
    funext fun ω => by rw [iInf_subtype']
  rw [h]
  exact Measurable.iInf fun d => hF d.1

theorem measurableSet_denseGoodSet (μ : Ω → Measure ℂ)
    (hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(μ ω))
    {D : Set ℂ} (hDc : D.Countable) (c₀ C r : ℝ) (z : ℂ) :
    MeasurableSet[m'] (denseGoodSet D μ c₀ C r z) := by
  have hA : IsOpen (HarmonicBalls.annulus z r (2 * r)) := isOpen_ball.sdiff isClosed_closedBall
  have hAm : MeasurableSet (HarmonicBalls.annulus z r (2 * r)) := hA.measurableSet
  have hS : (D ∩ HarmonicBalls.annulus z r (2 * r)).Countable := hDc.mono inter_subset_left
  have hint : ∀ d : ℂ, Measurable fun u : ℂ => ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) := fun d =>
    ((measurable_const.div ((measurable_id.sub measurable_const).norm)).log.add_const 1).ennreal_ofReal
  have hX : Measurable[m'] fun ω => ⨆ d ∈ D ∩ HarmonicBalls.annulus z r (2 * r),
      ∫⁻ u in HarmonicBalls.annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂(μ ω) :=
    measurable_iSup_dense hS (fun d ω => ∫⁻ u in HarmonicBalls.annulus z r (2 * r),
      ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂(μ ω))
      (fun d => measurable_lintegral_set μ hκ hAm (hint d))
  have hY : Measurable[m'] fun ω => ⨅ q ∈ D ∩ HarmonicBalls.annulus z r (2 * r),
      μ ω (Metric.ball q (c₀ / 2 * r)) :=
    measurable_iInf_dense hS (fun q ω => μ ω (Metric.ball q (c₀ / 2 * r)))
      (fun q => measurable_measure_set μ hκ measurableSet_ball)
  exact measurableSet_le hX (measurable_const.mul hY)

/-- A countable family of conditions indexed by `n : ℕ`, guarded by a proposition `p`, is measurable. -/
theorem measurableSet_imp_exists (p : Prop) (Q : ℕ → Prop) (S : ℕ → Set Ω) (hS : ∀ n, MeasurableSet[m'] (S n)) :
    MeasurableSet[m'] {ω : Ω | p → ∃ n, Q n ∧ ω ∈ S n} := by
  by_cases hp : p
  · have h : {ω : Ω | p → ∃ n, Q n ∧ ω ∈ S n} = ⋃ n : ℕ, ({ω : Ω | Q n} ∩ S n) := by
      ext ω
      simp only [hp, true_implies, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [h]
    exact MeasurableSet.iUnion fun n => (MeasurableSet.const (Q n)).inter (hS n)
  · have h : {ω : Ω | p → ∃ n, Q n ∧ ω ∈ S n} = univ := by
      ext ω
      simp [hp]
    rw [h]
    exact MeasurableSet.univ

/-- The dense cover event is field-measurable: the uncountable grid condition reduces to the countable index `(m, n) ∈ ℤ²`. -/
theorem measurableSet_denseCoverSet (μ : Ω → Measure ℂ)
    (hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(μ ω))
    {D : Set ℂ} (hDc : D.Countable) (ρ c₀ C δ : ℝ) :
    MeasurableSet[m'] (denseCoverSet D μ ρ c₀ C δ) := by
  have key : denseCoverSet D μ ρ c₀ C δ =
      ⋂ m : ℤ, ⋂ n : ℤ, {ω : Ω | (((δ / 100 : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∈
          Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt δ) \ Metric.ball (0 : ℂ) (10 * Real.sqrt δ) →
        ∃ k : ℕ, ((δ ≤ (7 : ℝ)⁻¹ ^ k ∧ (7 : ℝ)⁻¹ ^ k ≤ Real.sqrt δ) ∧
          ω ∈ denseGoodSet D μ c₀ C ((7 : ℝ)⁻¹ ^ k) (((δ / 100 : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)))} := by
    ext ω
    simp only [denseCoverSet, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h m n hz
      obtain ⟨r, h1, h2, ⟨k, rfl⟩, hG⟩ := h _ hz ⟨m, n, rfl⟩
      exact ⟨k, ⟨h1, h2⟩, hG⟩
    · intro h z hz hzg
      obtain ⟨m, n, rfl⟩ := hzg
      obtain ⟨k, ⟨h1, h2⟩, hG⟩ := h m n hz
      exact ⟨(7 : ℝ)⁻¹ ^ k, h1, h2, ⟨k, rfl⟩, hG⟩
  rw [key]
  refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun n => ?_
  exact measurableSet_imp_exists _ _ _ fun k => measurableSet_denseGoodSet μ hκ hDc _ _ _ _

end Measurability

/-- **Lemma 2, eq (9), from the dense minorant** (LEMMA68 Lemma 2 item 2, gap G9 closed except for the random-measure
hypothesis `hκ`). Given the Draft polynomial bound at constant `c₀ / 2` (`hpoly`, from `GoodAnnulusPrevalenceStmt`), the dense
cover at constant `C` is a field-measurable minorant of the printed cover at radius `c₀`, so the dyadic good-radius
conclusion holds on a field-measurable cutoff. -/
theorem goodAnnulusCover_dyadic_of_dense {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (hκ : ∀ f : ℂ → ℝ≥0∞, Measurable f → Measurable[m'] fun ω => ∫⁻ u, f u ∂(μ ω))
    {D : Set ℂ} (hD : Dense D) (hDc : D.Countable) {ρ c₀ C : ℝ} (hc₀ : 0 < c₀)
    (hpoly : HarmonicBalls.PolyHighProb P (fun δ => GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C δ)) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ∀ z : ℂ,
        z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \
          Metric.ball (0 : ℂ) (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) →
        (∃ m k : ℤ, z = ((((1 / 2 : ℝ) ^ n) / 100 : ℝ) : ℂ) * (m + k * Complex.I)) →
        ∃ r : ℝ, (1 / 2 : ℝ) ^ n ≤ r ∧ r ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulusEvent (μ ω) c₀ C r z := by
  have hsubE : ∀ n : ℕ, GoodRadiusCover.GoodAnnulusCoverEvent μ ρ (c₀ / 2) C ((1 / 2 : ℝ) ^ n) ⊆
      denseCoverSet D μ ρ c₀ C ((1 / 2 : ℝ) ^ n) := by
    intro n ω hω z hz hzg
    obtain ⟨r, h1, h2, h3, hG⟩ := hω z hz hzg
    exact ⟨r, h1, h2, h3, CoverMinorant.dense_of_good (D := D) (μ ω) hG⟩
  have hF : ∃ F : ℕ → Set Ω, (∀ n : ℕ, MeasurableSet[m'] (F n)) ∧
      (∀ n : ℕ, F n ⊆ GoodRadiusCover.GoodAnnulusCoverEvent μ ρ c₀ C ((1 / 2 : ℝ) ^ n)) ∧
      ∑' n : ℕ, P (F n)ᶜ ≠ ∞ := by
    refine ⟨fun n => denseCoverSet D μ ρ c₀ C ((1 / 2 : ℝ) ^ n),
      fun n => measurableSet_denseCoverSet μ hκ hDc _ _ _ _, fun n => ?_, ?_⟩
    · intro ω hω z hz hzg
      obtain ⟨r, h1, h2, h3, hG⟩ := hω z hz hzg
      have hr : 0 < r := lt_of_lt_of_le (by positivity) h1
      exact ⟨r, h1, h2, h3, CoverMinorant.good_of_dense hD hr hc₀ (μ ω) hG⟩
    · refine ne_top_of_le_ne_top (ConstantOrderDiv.tsum_dyadic_ne_top hpoly)
        (ENNReal.tsum_le_tsum fun n => measure_mono (compl_subset_compl.2 (hsubE n)))
  exact GoodRadiusCover.goodAnnulusCover_dyadic_of_minorant μ hF

end CoverMinorantMeasurable

end MatedCRT

#print axioms MatedCRT.CoverMinorantMeasurable.goodAnnulusCover_dyadic_of_dense
#print axioms MatedCRT.CoverMinorantMeasurable.measurableSet_denseCoverSet
