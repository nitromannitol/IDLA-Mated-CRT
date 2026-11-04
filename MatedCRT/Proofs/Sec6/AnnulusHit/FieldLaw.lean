import MatedCRT.Proofs.Field.WholePlaneCircleLaw
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Locality
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.EventCountable

/-!
# The law of a whole-plane good-annulus event

The dyadic circle averages determine every compactly supported test integral of
the LQG measure. The countable criterion for the good-annulus event therefore
transfers its law between whole-plane realizations. The whole-plane circle-law
bridge uses Leonardo Bonanno's circle-average interface.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set Metric Topology HarmonicBalls
open scoped ENNReal

abbrev CircleIndex := Set.Ioi (0 : ℝ) × ℂ

/-- A measurable version of the dyadic LQG test integral as a function of the
positive-radius circle-average process. -/
noncomputable def circleLQGIntegral (γ : ℝ) (g : ℂ → ℝ) (x : CircleIndex → ℝ) : ℝ :=
  limsup (fun k : ℕ => ∫ z, g z * (dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * AnnulusLocality.gridVersion
      (fun z x => x (⟨dyadicScale k, dyadicScale_pos k⟩, z)) x z))) atTop

theorem measurable_circleLQGIntegral (γ : ℝ) {g : ℂ → ℝ} (hg : Continuous g) :
    Measurable (circleLQGIntegral γ g) := by
  apply AnnulusLocality.measurable_limsup_of
  intro k
  exact AnnulusLocality.measurable_integral_gridVersion (fun z => measurable_pi_apply _) hg _ _

/-- On the continuous-path event, the grid version recovers the field. -/
theorem gridVersion_circle_eq {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (k : ℕ) (z : ℂ) :
    AnnulusLocality.gridVersion (fun (z : ℂ) (x : CircleIndex → ℝ) =>
      x (⟨dyadicScale k, dyadicScale_pos k⟩, z))
      (fun p => hcirc ω p.1 p.2) z = hcirc ω (dyadicScale k) z := by
  have hc : Continuous (fun z => hcirc ω (dyadicScale k) z) :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨dyadicScale_pos k, mem_univ z⟩
  exact ((hc.tendsto z).comp (AnnulusLocality.tendsto_gridPt z)).limsup_eq

/-- The measurable functional equals integration against the LQG measure almost surely. -/
theorem circleLQGIntegral_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∀ᵐ ω ∂P, circleLQGIntegral γ g (fun p => hcirc ω p.1 p.2) = ∫ z, g z ∂(μ ω) := by
  filter_upwards [h.ae_continuousOn_circle, hμ] with ω hcont hlim
  have hc (k : ℕ) : Continuous (fun z => hcirc ω (dyadicScale k) z) :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨dyadicScale_pos k, mem_univ z⟩
  have hI (k : ℕ) : (∫ z, g z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * AnnulusLocality.gridVersion
        (fun (z : ℂ) (x : CircleIndex → ℝ) => x (⟨dyadicScale k, dyadicScale_pos k⟩, z))
        (fun p => hcirc ω p.1 p.2) z))) = ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) := by
    have hm : Measurable fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale k) z)) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc k)))).measurable.ennreal_ofReal
    rw [lqgApprox, integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    have hscale : 0 < dyadicScale k := dyadicScale_pos k
    rw [gridVersion_circle_eq hcirc ω hcont k z, ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul, mul_comm]
  unfold circleLQGIntegral
  have ht := hlim.tendsto_integral g hg hgc
  exact (Tendsto.congr (fun k => (hI k).symm) ht).limsup_eq

/-- The good-annulus event as a measurable condition on circle averages. -/
def circleGoodAnnulusCriterion (γ c₀ C r : ℝ) (z : ℂ) : Set (CircleIndex → ℝ) :=
  {x | (fun j : AnnulusEventCountable.Index =>
    circleLQGIntegral γ (AnnulusEventCountable.testFn z r c₀ j) x) ∈
      AnnulusEventCountable.criterion z r C}

theorem measurableSet_circleGoodAnnulusCriterion {r : ℝ} (hr : 0 < r)
    (γ c₀ C : ℝ) (z : ℂ) : MeasurableSet (circleGoodAnnulusCriterion γ c₀ C r z) := by
  apply (AnnulusEventCountable.measurableSet_criterion z r C).preimage
  exact Measurable.of_eval fun j =>
    measurable_circleLQGIntegral γ (AnnulusEventCountable.testFn_properties hr z j).1

theorem goodAnnulus_ae_iff_circleCriterion {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {r c₀ : ℝ} (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (C : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, IsGoodAnnulusEvent (μ ω) c₀ C r z ↔
      (fun p : CircleIndex => hcirc ω p.1 p.2) ∈ circleGoodAnnulusCriterion γ c₀ C r z := by
  have htest : ∀ᵐ ω ∂P, ∀ j : AnnulusEventCountable.Index,
      circleLQGIntegral γ (AnnulusEventCountable.testFn z r c₀ j)
        (fun p => hcirc ω p.1 p.2) = ∫ u, AnnulusEventCountable.testFn z r c₀ j u ∂(μ ω) := by
    apply ae_all_iff.2
    intro j
    exact circleLQGIntegral_ae h hμ (AnnulusEventCountable.testFn_properties hr z j).1
      (AnnulusEventCountable.testFn_properties hr z j).2.1
  filter_upwards [htest, hμ] with ω htest hlim
  let _ : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  rw [AnnulusEventCountable.isGoodAnnulusEvent_iff_criterion hr hc₀ C z (μ ω)]
  have heq : (fun j : AnnulusEventCountable.Index =>
      circleLQGIntegral γ (AnnulusEventCountable.testFn z r c₀ j)
        (fun p => hcirc ω p.1 p.2)) =
      (fun j => ∫ u, AnnulusEventCountable.testFn z r c₀ j u ∂(μ ω)) := funext htest
  exact Iff.of_eq (congrArg (fun q => q ∈ AnnulusEventCountable.criterion z r C) heq).symm

/-- The probability of a good-annulus event is independent of the realization
of the whole-plane GFF and its LQG measure. -/
theorem wholePlane_goodAnnulus_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (h' : IsWholePlaneGFF P' hC' hcirc') (hμ' : IsLQGMeasure P' γ hcirc' μ')
    {r c₀ : ℝ} (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (C : ℝ) (z : ℂ) :
    P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} =
      P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C r z} := by
  let T : Ω → CircleIndex → ℝ := fun ω p => hcirc ω p.1 p.2
  let T' : Ω' → CircleIndex → ℝ := fun ω p => hcirc' ω p.1 p.2
  let S := circleGoodAnnulusCriterion γ c₀ C r z
  have hTm : Measurable T := Measurable.of_eval fun p => h.measurable_circle p.1 p.2 p.1.2
  have hTm' : Measurable T' := Measurable.of_eval fun p => h'.measurable_circle p.1 p.2 p.1.2
  have hS : MeasurableSet S := measurableSet_circleGoodAnnulusCriterion hr γ c₀ C z
  have heq : {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} =ᵐ[P] T ⁻¹' Sᶜ := by
    filter_upwards [goodAnnulus_ae_iff_circleCriterion h hμ hr hc₀ C z] with ω hω
    exact propext (not_congr hω)
  have heq' : {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C r z} =ᵐ[P'] T' ⁻¹' Sᶜ := by
    filter_upwards [goodAnnulus_ae_iff_circleCriterion h' hμ' hr hc₀ C z] with ω hω
    exact propext (not_congr hω)
  calc
    P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} = P (T ⁻¹' Sᶜ) := measure_congr heq
    _ = (P.map T) Sᶜ := (Measure.map_apply hTm hS.compl).symm
    _ = (P'.map T') Sᶜ := by rw [wholePlane_circle_law h h']
    _ = P' (T' ⁻¹' Sᶜ) := Measure.map_apply hTm' hS.compl
    _ = P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C r z} := (measure_congr heq').symm

end MatedCRT.Field
