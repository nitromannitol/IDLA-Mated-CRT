import MatedCRT.FirstPass.Derived.HN8TransferOfGoodSet
import MatedCRT.FirstPass.Derived.ReferenceEnvMeasurableVersion
import LatticeProb.Prob.AnalyticImageMeasurableKernel
import LatticeProb.MeasureTheory.RectangleTentUniqueness

/-!
# The law-a.e. Markov and invariance statement from a reference environment

`ae_markovTCBM_invariant_of_goodCoordSet` reduces the law-a.e. statement `hN8'` (the Liouville Brownian motion law
field is a Markovian time-changed Brownian motion with invariant measure the LQG measure, for almost every pair of
field coordinates and LQG data) to a measurable set of field coordinates of full `quantumConeCoordLaw γ` measure on
which a good locally finite measure exists, and to a countable test family determining locally finite measures.

This file supplies both.

* The test family is the family of tents `w ↦ max 0 (1 - dist(w, R) / δ)` over closed rectangles `R` with rational
  corners at rational widths `δ > 0` (`ratRectTent`); they determine locally finite measures on `ℂ` by
  `LatticeProb.Complex.ext_of_integral_tent_ratRectangle`.
* The good set is obtained from one valid environment `S₀` on `ℝ` with a measurable field version `H₀`: if almost
  surely the law field at the coordinates `pairJ ⊤ (H₀ r)` is a Markovian time-changed Brownian motion with
  invariant measure `S₀.μ r`, then the image under `r ↦ pairJ ⊤ (H₀ r)` of a measurable set of full measure on which
  this holds contains a measurable set of full image measure
  (`LatticeProb.exists_measurableSet_subset_image_measure_preimage_compl_eq_zero`, `ℝ` being standard Borel), and the
  image measure is `quantumConeCoordLaw γ`.

`markovTCBM_invariant_law_of_referenceEnvironments` combines this with the reference environments of the model:
`hN8'`, exactly as typed, follows from the almost sure statement for valid environments on `ℝ`.
-/

open MeasureTheory Filter Topology Set Metric
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure IsDyadicVagueLimitAlong)

namespace MatedCRT

/-- Indices of the rational rectangle tents: corners `a ≤ b`, `c ≤ d` and a width `δ > 0`, all rational, stored as
`(a, b, c, d, δ)`. -/
abbrev RatRectTentIndex : Type :=
  {p : ℚ × ℚ × ℚ × ℚ × ℚ // p.1 ≤ p.2.1 ∧ p.2.2.1 ≤ p.2.2.2.1 ∧ 0 < p.2.2.2.2}

/-- The tent of width `δ` over the closed rectangle `[a, b] ×ℂ [c, d]`: `w ↦ max 0 (1 - dist(w, R) / δ)`. -/
noncomputable def ratRectTent (i : RatRectTentIndex) (w : ℂ) : ℝ :=
  max 0 (1 - infDist w (Complex.reProdIm (Icc (i.1.1 : ℝ) i.1.2.1) (Icc (i.1.2.2.1 : ℝ) i.1.2.2.2.1)) /
    (i.1.2.2.2.2 : ℝ))

theorem continuous_ratRectTent (i : RatRectTentIndex) : Continuous (ratRectTent i) :=
  continuous_const.max (continuous_const.sub ((continuous_infDist_pt _).div_const _))

theorem ratRectTent_nonneg (i : RatRectTentIndex) (w : ℂ) : 0 ≤ ratRectTent i w :=
  le_max_left _ _

/-- A rectangle tent vanishes outside the closed `δ`-thickening of its (nonempty, compact) rectangle. -/
theorem hasCompactSupport_ratRectTent (i : RatRectTentIndex) : HasCompactSupport (ratRectTent i) := by
  obtain ⟨⟨a, b, c, d, δ⟩, hab, hcd, hδ⟩ := i
  have hR : IsCompact (Complex.reProdIm (Icc (a : ℝ) b) (Icc (c : ℝ) d)) :=
    LatticeProb.Complex.isCompact_Icc_reProdIm_Icc _ _ _ _
  have hne : (Complex.reProdIm (Icc (a : ℝ) b) (Icc (c : ℝ) d)).Nonempty :=
    ⟨⟨(a : ℝ), (c : ℝ)⟩, Complex.mem_reProdIm.2
      ⟨left_mem_Icc.2 (by exact_mod_cast hab), left_mem_Icc.2 (by exact_mod_cast hcd)⟩⟩
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine HasCompactSupport.intro (hR.cthickening (r := δ)) fun w hw => ?_
  have hle : (δ : ℝ) ≤ infDist w (Complex.reProdIm (Icc (a : ℝ) b) (Icc (c : ℝ) d)) :=
    not_lt.1 fun hlt => hw (thickening_subset_cthickening _ _ ((mem_thickening_iff_infDist_lt hne).2 hlt))
  have h1 : 1 ≤ infDist w (Complex.reProdIm (Icc (a : ℝ) b) (Icc (c : ℝ) d)) / (δ : ℝ) := by
    rw [le_div_iff₀ hδ', one_mul]
    exact hle
  exact max_eq_left (sub_nonpos.2 h1)

/-- **The rational rectangle tents determine locally finite measures on `ℂ`.** -/
theorem ext_of_integral_ratRectTent (ν ν' : Measure ℂ) (hν : IsLocallyFiniteMeasure ν)
    (hν' : IsLocallyFiniteMeasure ν') (h : ∀ i, ∫ w, ratRectTent i w ∂ν = ∫ w, ratRectTent i w ∂ν') :
    ν = ν' :=
  LatticeProb.Complex.ext_of_integral_tent_ratRectangle fun a b c d hab hcd δ hδ =>
    h ⟨(a, b, c, d, δ), hab, hcd, hδ⟩

/-- **The law-a.e. Markov and invariance statement from one reference environment.**
Let `S₀` be a valid environment on `ℝ` with a measurable version `H₀` of its field, such that almost surely the law
field `lbmPathLawField γ` at the field coordinates `pairJ ⊤ (H₀ r)` is a Markovian time-changed Brownian motion with
invariant measure `S₀.μ r`. Then for every valid environment `S`, every measurable version `H` of its field and
every measurable encoding `E` of its LQG measure, the same holds for almost every pair `(x, e)` under the law of
`(pairJ ⊤ (H ω), E ω)`, with invariant measure `toMeasure e`. -/
theorem ae_markovTCBM_invariant_of_referenceEnv {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {S₀ : MatedCRTEnv ℝ} (hS₀ : S₀.IsValid 𝒮 γ) {H₀ : ℝ → LQGMetric.DistC}
    (hH₀ : Measurable H₀) (hrep₀ : ∀ᵐ r ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC r φ = H₀ r φ)
    (hgood₀ : ∀ᵐ r ∂S₀.P, IsMarkovTCBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) ∧
      IsInvariantFor (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) (S₀.μ r))
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hEm : Measurable E) (hE : ∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) :
    ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
      IsMarkovTCBM (lbmPathLawField γ d.1) ∧
        IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) := by
  have : IsProbabilityMeasure S₀.P := hS₀.isProbabilityMeasure
  have hx₀ : Measurable fun r => LQGMetric.pairJ ⊤ (H₀ r) := measurable_pairJ_top.comp hH₀
  -- almost surely the field coordinates of `S₀` lie in the (possibly non-measurable) good set
  have hG : ∀ᵐ r ∂S₀.P, ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧
      IsDyadicVagueLimitAlong γ ratRectTent (LQGMetric.pairJ ⊤ (H₀ r)) μ ∧
      IsMarkovTCBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) ∧
      IsInvariantFor (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) μ := by
    filter_upwards [hS₀.ae_isLQGLimit_coordCircleAverage hγ0 hγ2 hrep₀, hgood₀] with r hr hg
    exact ⟨S₀.μ r, hr.isLocallyFiniteMeasure,
      fun i => hr.tendsto_integral _ (continuous_ratRectTent i) (hasCompactSupport_ratRectTent i), hg.1, hg.2⟩
  -- a measurable set of full measure inside it, and a measurable set of full image measure inside its image
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hG)
  obtain ⟨A, hAW, hAm, hA0⟩ :=
    LatticeProb.exists_measurableSet_subset_image_measure_preimage_compl_eq_zero S₀.P hx₀ hTm.compl
      (by rwa [compl_compl])
  refine ae_markovTCBM_invariant_of_goodCoordSet hγ0 hγ2 ratRectTent continuous_ratRectTent
    hasCompactSupport_ratRectTent ratRectTent_nonneg ext_of_integral_ratRectTent hAm ?_ ?_ hS hH hrep hEm hE
  · rw [← hS₀.map_pairJ_eq_quantumConeCoordLaw hH₀ hrep₀, Measure.map_apply hx₀ hAm.compl]
    exact hA0
  · intro x hx
    obtain ⟨r, hrW, rfl⟩ := hAW hx
    by_contra hxG
    exact hrW (hTsub hxG)

/-- **`hN8'` from the almost sure statement for valid environments on `ℝ`.** If the model has valid reference
environments, and for every `γ ∈ (0, 2)`, every valid environment `S₀` on `ℝ` and every measurable version `H₀` of
its field, almost surely the law field at `pairJ ⊤ (H₀ r)` is a Markovian time-changed Brownian motion with
invariant measure `S₀.μ r`, then the law-a.e. statement `hN8'` holds, exactly as typed. -/
theorem markovTCBM_invariant_law_of_referenceEnvironments {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮)
    (hgood : ∀ γ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ r ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC r φ = H₀ r φ) →
      ∀ᵐ r ∂S₀.P, IsMarkovTCBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) ∧
        IsInvariantFor (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ r))) (S₀.μ r)) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) := by
  intro γ hγ0 hγ2 Ω _ S hS H hH hrep E hEm hE
  obtain ⟨S₀, hS₀, H₀, hH₀, hrep₀⟩ := exists_referenceEnv_measurable_fieldVersion h10 hγ0 hγ2
  exact ae_markovTCBM_invariant_of_referenceEnv hγ0 hγ2 hS₀ hH₀ hrep₀ (hgood γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep₀) hS hH
    hrep hEm hE

end MatedCRT
