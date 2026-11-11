import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.HoneModelInputs68
import MatedCRT.FirstPass.S6f.UniformEvents
import MatedCRT.FirstPass.SLERef.Certified

/-!
# One exponent for the exit-time event and the counting good event

`CountingAtExitAlphaStmt 𝒮` (Guard68S10) asks for one pair `(α, β)` such that the exit-time event
`exitTimeEvent68 S α ρ CE` (Draft Lemma 2.18, `ExitTimeUpperBoundStmt`) and the counting good event
`countingGoodEvent S α β ρ` (Draft Lemma 2.9, `CountingMeasureConvergenceStmt`) both have polynomially high probability.
The two Draft statements give their own exponents `αE` and `αC`.

Both events shrink as the exponent decreases (for `0 < ε ≤ 1`): the exit-time event at `α₁` implies it at `α₂ ≤ α₁`,
and the counting event at `α₁` implies it at `α₂ ≤ α₁` on the almost sure event where the LQG measure is locally finite.
Taking `α := min αC αE` therefore gives one exponent for both. The monotonicity lemmas below are elementary inequalities
(compare `greenLowEvent68_subset_of_le`, Uniform68Monotone.lean:22); they are not stated in the paper, which uses the same
`α` by fiat at its proof (line 3820).

The first-pass entry point `countingAtExitAlphaStmt_of_firstPass` takes exactly the hypothesis of the first-pass
projections `CertifiedReferenceModel.countingMeasureConvergence` and `CertifiedReferenceModel.exitTimeUpperBound`
(SLERef/Certified.lean:103, :135).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal
open HarmonicBalls

namespace MatedCRT
namespace CountingExitAlpha68

variable {Ω : Type} [MeasurableSpace Ω]

/-- The largest exit time `𝓜(D) = sup_{z ∈ D} ∫_D log(1/|z - w|) + 1 dμ(w)` is monotone in the set. -/
theorem largestExitTimeRV_mono_set (μ : Measure ℂ) {D₁ D₂ : Set ℂ} (h : D₁ ⊆ D₂) :
    largestExitTimeRV μ D₁ ≤ largestExitTimeRV μ D₂ := by
  unfold largestExitTimeRV
  refine iSup₂_le fun z hz => ?_
  exact (lintegral_mono_set h).trans
    (le_iSup₂ (f := fun z (_ : z ∈ D₂) => ∫⁻ w in D₂, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) z (h hz))

/-- Decreasing the exit exponent weakens the exit-time event `exitTimeEvent68` (for `0 < ε ≤ 1`). -/
theorem exitTimeEvent68_subset_of_le (S : MatedCRTEnv Ω) {α₁ α₂ ρ CE ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (h : α₂ ≤ α₁) :
    exitTimeEvent68 S α₁ ρ CE ε ⊆ exitTimeEvent68 S α₂ ρ CE ε := by
  rintro ω ⟨h1, h2⟩
  have hpow : ε ^ α₁ ≤ ε ^ α₂ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 h
  have hthick : ∀ D : Set ℂ, thickening (ε ^ α₁) D ⊆ thickening (ε ^ α₂) D :=
    fun D => thickening_mono hpow D
  refine ⟨fun D hD hDB hμ a ha N => ?_, fun D hDB a ha => ?_⟩
  · have hμ₁ : ENNReal.ofReal (ε ^ α₁) ≤ S.μ ω D := (ENNReal.ofReal_le_ofReal hpow).trans hμ
    have hint : (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α₁) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω)
        ≤ ⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α₂) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω :=
      iSup₂_mono fun z _ => lintegral_mono_set (hthick D)
    exact (h1 D hD hDB hμ₁ a ha N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hint N) (by positivity))
  · obtain ⟨hn, he⟩ := h2 D hDB a ha
    exact ⟨hn, he.trans (mul_le_mul_of_nonneg_left (largestExitTimeRV_mono_set _ (hthick D)) (by positivity))⟩

/-- Decreasing the counting exponent weakens the counting good event `countingGoodEvent` (for `0 < ε ≤ 1`), at every
`ω` whose LQG measure is locally finite. The integrals of `f` are over the thickenings, where `f` is bounded and
Lipschitz by the hypotheses of the event, hence continuous and integrable. -/
theorem countingGoodEvent_mem_of_le (S : MatedCRTEnv Ω) {α₁ α₂ β ρ ε : ℝ} {ω : Ω}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (h : α₂ ≤ α₁) (hloc : IsLocallyFiniteMeasure (S.μ ω))
    (hω : ω ∈ HoneModelInputs68.countingGoodEvent S α₁ β ρ ε) :
    ω ∈ HoneModelInputs68.countingGoodEvent S α₂ β ρ ε := by
  intro D f w hD hf hLip hw
  have hpow : ε ^ α₁ ≤ ε ^ α₂ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 h
  have hthick : thickening (ε ^ α₁) D ⊆ thickening (ε ^ α₂) D := thickening_mono hpow D
  have hf1 : ∀ x ∈ thickening (ε ^ α₁) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β) :=
    fun x hx => hf x (hthick hx)
  have hLip1 : ∀ x ∈ thickening (ε ^ α₁) D, ∀ y ∈ thickening (ε ^ α₁) D,
      |f x - f y| ≤ ε ^ (-β) * ‖x - y‖ :=
    fun x hx y hy => hLip x (hthick hx) y (hthick hy)
  obtain ⟨h1l, h1u⟩ := hω D f w hD hf1 hLip1 hw
  -- integrability of `f` on the larger thickening
  have hopen : MeasurableSet (thickening (ε ^ α₂) D) := Metric.isOpen_thickening.measurableSet
  have hb : Bornology.IsBounded (thickening (ε ^ α₂) D) :=
    (Metric.isBounded_ball.subset hD).thickening
  have hloc' := hloc
  have hfin : S.μ ω (thickening (ε ^ α₂) D) ≠ ⊤ :=
    ne_top_of_le_ne_top (hb.isCompact_closure.measure_lt_top.ne) (measure_mono subset_closure)
  have hcont : ContinuousOn f (thickening (ε ^ α₂) D) := by
    have hL : LipschitzOnWith (Real.toNNReal (ε ^ (-β))) f (thickening (ε ^ α₂) D) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (Real.rpow_nonneg hε0.le _)]
      exact hLip x hx y hy
    exact hL.continuousOn
  have hint_int : IntegrableOn f (thickening (ε ^ α₂) D) (S.μ ω) := by
    have hmeas : AEStronglyMeasurable f ((S.μ ω).restrict (thickening (ε ^ α₂) D)) :=
      hcont.aestronglyMeasurable hopen
    have : IsFiniteMeasure ((S.μ ω).restrict (thickening (ε ^ α₂) D)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
    refine (integrable_const (ε ^ (-β))).mono' hmeas ?_
    refine ae_restrict_of_forall_mem hopen fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact (hf x hx).2
  have hint_le : ∫ x in thickening (ε ^ α₁) D, f x ∂S.μ ω ≤ ∫ x in thickening (ε ^ α₂) D, f x ∂S.μ ω :=
    setIntegral_mono_set hint_int
      (ae_restrict_of_forall_mem hopen fun x hx => (hf x hx).1)
      (Filter.Eventually.of_forall fun x hx => hthick hx)
  have hexp : ε ^ (-1 + α₁) ≤ ε ^ (-1 + α₂) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hinv : 0 ≤ ε⁻¹ := inv_nonneg.2 hε0.le
  have hscaled := mul_le_mul_of_nonneg_left hint_le hinv
  constructor
  · linarith
  · linarith

/-- A polynomially high probability event stays so after adding a null set: if `E r ∩ G ⊆ F r` for `r < 1` and
`G` has full measure, then `F` has polynomially high probability. -/
theorem polyHighProb_of_ae_subset {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {E F : ℝ → Set Ω'}
    {G : Set Ω'} (h : HarmonicBalls.PolyHighProb P E) (hG : ∀ᵐ ω ∂P, ω ∈ G)
    (hEF : ∀ r : ℝ, 0 < r → r < 1 → E r ∩ G ⊆ F r) :
    HarmonicBalls.PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, min r₀ 1, lt_min hr₀ one_pos, fun r hr hrr => ?_⟩
  have hsub : (F r)ᶜ ⊆ (E r)ᶜ ∪ {ω | ω ∉ G} := by
    intro ω hω
    by_cases hE' : ω ∈ E r
    · by_cases hG' : ω ∈ G
      · exact absurd (hEF r hr (lt_of_lt_of_le hrr (min_le_right _ _)) ⟨hE', hG'⟩) hω
      · exact Or.inr hG'
    · exact Or.inl hE'
  calc P (F r)ᶜ ≤ P ((E r)ᶜ ∪ {ω | ω ∉ G}) := measure_mono hsub
    _ ≤ P (E r)ᶜ + P {ω | ω ∉ G} := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [ae_iff.1 hG, add_zero]
    _ ≤ _ := hE r hr (lt_of_lt_of_le hrr (min_le_left _ _))

/-- The one-exponent counting statement from the two Draft statements: the exit-time exponent `αE` and the counting
exponent `αC` are replaced by `min αC αE`, with the counting exponent `β` of `CountingMeasureConvergenceStmt`. -/
theorem countingAtExitAlphaStmt_of_counting_exit {𝒮 : SpaceFillingSLEModel}
    (hC : CountingMeasureConvergenceStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮) :
    Lemma68Guard10.CountingAtExitAlphaStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨αC, βC, hαC, hβC, hCnt⟩ := hC γ hγ hγ2
  obtain ⟨αE, hαE, hEx⟩ := hE γ hγ hγ2
  refine ⟨min αC αE, βC, lt_min hαC hαE, hβC, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CE, hCE, hEρ⟩ := hEx ρ hρ0 hρ1
  refine ⟨CE, hCE, fun Ω _ S hS => ⟨?_, ?_⟩⟩
  · refine PolyHighProb.mono_of_small (hEρ Ω S hS) one_pos fun ε h0 h1 => ?_
    exact exitTimeEvent68_subset_of_le S h0 h1.le (min_le_right _ _)
  · refine polyHighProb_of_ae_subset (G := {ω | IsLocallyFiniteMeasure (S.μ ω)}) (hCnt ρ hρ0 hρ1 Ω S hS) ?_ ?_
    · have hL : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
        filter_upwards [hS.isLQGMeasure] with ω hω using hω.isLocallyFiniteMeasure
      exact hL
    · intro ε h0 h1 ω hω
      exact countingGoodEvent_mem_of_le S h0 h1.le (min_le_left _ _) hω.2 hω.1

/-- **Counting exponent at the exit exponent.** The first-pass input is the
certified reference model, as for the projections `CertifiedReferenceModel.countingMeasureConvergence` and
`CertifiedReferenceModel.exitTimeUpperBound`. -/
theorem countingAtExitAlphaStmt_of_firstPass {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModel ν 𝒮) : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮 :=
  countingAtExitAlphaStmt_of_counting_exit (CertifiedReferenceModel.countingMeasureConvergence h)
    (CertifiedReferenceModel.exitTimeUpperBound h)

end CountingExitAlpha68
end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit
#print axioms MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass
