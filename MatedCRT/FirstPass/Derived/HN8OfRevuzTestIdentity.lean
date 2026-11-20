import MatedCRT.FirstPass.Derived.HN8OfRevuzIdentification
import LatticeProb.MeasureTheory.ExtOfLintegralCompactlySupported

/-!
# The Revuz identification from compactly supported test functions

`markovTCBM_invariant_law_of_revuz_identification` reduces the law-a.e. statement `hN8'` to the identification
`revuz planarLaw G = S₀.μ r` of the Revuz measure of a PCAF version `G` of the clock with the LQG measure. This file
reduces that identification to the equality of the integrals of nonnegative continuous compactly supported test
functions, in two quantifier orders.

* Uniform order (`ae_exists_revuz_eq_of_lintegral_eq`): almost surely, for some PCAF version `G` with a good clock,
  `∫⁻ f d(revuz planarLaw G) = ∫⁻ f dμ` for every test function `f`. The LQG measure is locally finite, and two
  measures, one of them locally finite, with equal integrals of all nonnegative continuous compactly supported
  functions are equal (`LatticeProb.ext_of_lintegral_ofReal_eq_of_hasCompactSupport`).
* Per-test-function order (`ae_forall_revuz_eq_of_ratRectTent`): for every test function `f`, almost surely, the
  identity holds for every adapted PCAF version with a good clock. Only the countable family of rational rectangle
  tents `ratRectTent` is used: equal tent integrals against a locally finite measure force local finiteness
  (`isFiniteMeasureOnCompacts_of_lintegral_ofReal_ratRectTent_lt_top`; the tent over a rectangle is `1` on it) and
  then equality (`eq_of_lintegral_ofReal_ratRectTent_eq`).

Both are wired to `hN8'`, exactly as typed.
-/

namespace MatedCRT

open MeasureTheory MarkovProcess
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)
open scoped NNReal ENNReal

/-- The rational rectangle tent equals `1` on its rectangle. -/
theorem ratRectTent_eq_one_of_mem (i : RatRectTentIndex) {w : ℂ}
    (hw : w ∈ Complex.reProdIm (Set.Icc (i.1.1 : ℝ) i.1.2.1) (Set.Icc (i.1.2.2.1 : ℝ) i.1.2.2.2.1)) :
    ratRectTent i w = 1 := by
  simp [ratRectTent, Metric.infDist_zero_of_mem hw]

/-- The square `[-n, n] ×ℂ [-n, n]` (with rational corners) contains every set of complex numbers of norm at
most `n`. -/
theorem subset_ratSquare_of_norm_le (n : ℕ) {K : Set ℂ} (hK : ∀ w ∈ K, ‖w‖ ≤ n) :
    K ⊆ Complex.reProdIm (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
      (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ)) := by
  intro w hw
  have h1 := hK w hw
  rw [Complex.mem_reProdIm]
  simp only [Rat.cast_neg, Rat.cast_natCast]
  exact ⟨abs_le.mp ((Complex.abs_re_le_norm w).trans h1), abs_le.mp ((Complex.abs_im_le_norm w).trans h1)⟩

/-- **Finite tent integrals force finiteness on compact sets.**  A measure on `ℂ` with finite integrals of all
rational rectangle tents is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_of_lintegral_ofReal_ratRectTent_lt_top {ν : Measure ℂ}
    (h : ∀ i, ∫⁻ w, ENNReal.ofReal (ratRectTent i w) ∂ν < ∞) : IsFiniteMeasureOnCompacts ν := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_ge C
  let i : RatRectTentIndex :=
    ⟨(-(n : ℚ), (n : ℚ), -(n : ℚ), (n : ℚ), 1), neg_le_self n.cast_nonneg, neg_le_self n.cast_nonneg, one_pos⟩
  have hKR := subset_ratSquare_of_norm_le n (K := K) fun w hw => by
    have := hC w hw
    rw [norm_norm] at this
    exact this.trans hn
  have hRm : MeasurableSet (Complex.reProdIm (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
      (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))) :=
    (LatticeProb.Complex.isCompact_Icc_reProdIm_Icc _ _ _ _).isClosed.measurableSet
  calc ν K ≤ ν (Complex.reProdIm (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
        (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))) := measure_mono hKR
    _ = ∫⁻ w, (Complex.reProdIm (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
        (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))).indicator 1 w ∂ν := (lintegral_indicator_one hRm).symm
    _ ≤ ∫⁻ w, ENNReal.ofReal (ratRectTent i w) ∂ν := by
      refine lintegral_mono fun w => ?_
      by_cases hw : w ∈ Complex.reProdIm (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
          (Set.Icc (((-(n : ℚ)) : ℚ) : ℝ) ((n : ℚ) : ℝ))
      · rw [Set.indicator_of_mem hw, ratRectTent_eq_one_of_mem i hw]
        simp
      · rw [Set.indicator_of_notMem hw]
        exact zero_le
    _ < ∞ := h i

/-- **Rational rectangle tents determine a measure next to a locally finite one.**  If a measure `ν` on `ℂ` and a
locally finite measure `μ` have the same integrals of all rational rectangle tents, then `ν = μ`. -/
theorem eq_of_lintegral_ofReal_ratRectTent_eq {ν μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (h : ∀ i, ∫⁻ w, ENNReal.ofReal (ratRectTent i w) ∂ν = ∫⁻ w, ENNReal.ofReal (ratRectTent i w) ∂μ) :
    ν = μ := by
  have hμi : ∀ i, Integrable (ratRectTent i) μ := fun i =>
    (continuous_ratRectTent i).integrable_of_hasCompactSupport (hasCompactSupport_ratRectTent i)
  have : IsFiniteMeasureOnCompacts ν :=
    isFiniteMeasureOnCompacts_of_lintegral_ofReal_ratRectTent_lt_top fun i =>
      (h i).trans_lt (hμi i).lintegral_lt_top
  have hconv : ∀ (m : Measure ℂ) (i : RatRectTentIndex),
      ∫ w, ratRectTent i w ∂m = (∫⁻ w, ENNReal.ofReal (ratRectTent i w) ∂m).toReal := fun m i =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => ratRectTent_nonneg i w)
      (continuous_ratRectTent i).aestronglyMeasurable
  exact ext_of_integral_ratRectTent ν μ inferInstance inferInstance fun i => by rw [hconv, hconv, h i]

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}

/-- **The Revuz identification from test functions, uniform order.**  If almost surely some PCAF version `G` of the
clock with a good clock satisfies `∫⁻ f d(revuz planarLaw G) = ∫⁻ f dμ` for every nonnegative continuous compactly
supported `f`, then almost surely `revuz planarLaw G = S.μ ω` for that version. -/
theorem ae_exists_revuz_eq_of_lintegral_eq (hS : S.IsValid 𝒮 γ)
    (h : ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → 0 ≤ f →
        ∫⁻ x, ENNReal.ofReal (f x) ∂(revuz planarLaw G) = ∫⁻ x, ENNReal.ofReal (f x) ∂(S.μ ω)) :
    ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) ∧ revuz planarLaw G = S.μ ω := by
  filter_upwards [h, hS.isLQGMeasure] with ω hω hμ
  obtain ⟨G, hA, hG, hGc, hf⟩ := hω
  have := hμ.isLocallyFiniteMeasure
  exact ⟨G, hA, hG, hGc, LatticeProb.ext_of_lintegral_ofReal_eq_of_hasCompactSupport hf⟩

/-- **The Revuz identification from test functions, per-test-function order.**  If for every rational rectangle
tent, almost surely, its integrals against the Revuz measure of every adapted PCAF version of the clock with a good
clock and against `S.μ ω` agree, then almost surely `revuz planarLaw G = S.μ ω` for all such versions. -/
theorem ae_forall_revuz_eq_of_ratRectTent (hS : S.IsValid 𝒮 γ)
    (h : ∀ i : RatRectTentIndex, ∀ᵐ ω ∂S.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G →
      GoodClock planarLaw G → (∀ t, Measurable[pathFiltration t] (G t)) →
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) →
      ∫⁻ x, ENNReal.ofReal (ratRectTent i x) ∂(revuz planarLaw G) =
        ∫⁻ x, ENNReal.ofReal (ratRectTent i x) ∂(S.μ ω)) :
    ∀ᵐ ω ∂S.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G → GoodClock planarLaw G →
      (∀ t, Measurable[pathFiltration t] (G t)) →
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) → revuz planarLaw G = S.μ ω := by
  filter_upwards [ae_all_iff.2 h, hS.isLQGMeasure] with ω hω hμ G hA hG hGa hGc
  have := hμ.isLocallyFiniteMeasure
  exact eq_of_lintegral_ofReal_ratRectTent_eq fun i => hω i G hA hG hGa hGc

end ValidEnvironment

/-- **`hN8'` from the test-function identity, uniform order.**  Given the reference environments of the model,
`hN8'` holds, exactly as typed, as soon as every valid environment `S₀` on `ℝ` satisfies: almost surely some PCAF
version of its clock with a good clock has the integrals of all nonnegative continuous compactly supported functions
against its Revuz measure equal to those against `S₀.μ r`. -/
theorem markovTCBM_invariant_law_of_revuz_lintegral_identification {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮)
    (hT : ∀ γ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ᵐ r ∂S₀.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
        (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S₀.clock r b t) ∧
        ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → 0 ≤ f →
          ∫⁻ x, ENNReal.ofReal (f x) ∂(revuz planarLaw G) = ∫⁻ x, ENNReal.ofReal (f x) ∂(S₀.μ r)) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) :=
  markovTCBM_invariant_law_of_revuz_identification h10 fun γ hγ0 hγ2 S₀ hS₀ =>
    ae_exists_revuz_eq_of_lintegral_eq hS₀ (hT γ hγ0 hγ2 S₀ hS₀)

/-- **`hN8'` from the test-function identity, per-test-function order.**  As
`markovTCBM_invariant_law_of_revuz_lintegral_identification`, with the identity asked, for each nonnegative continuous
compactly supported `f` separately, almost surely for every adapted PCAF version of the clock with a good clock. -/
theorem markovTCBM_invariant_law_of_forall_revuz_lintegral_identification {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮)
    (hT : ∀ γ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → 0 ≤ f →
      ∀ᵐ r ∂S₀.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G → GoodClock planarLaw G →
        (∀ t, Measurable[pathFiltration t] (G t)) →
        (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S₀.clock r b t) →
        ∫⁻ x, ENNReal.ofReal (f x) ∂(revuz planarLaw G) = ∫⁻ x, ENNReal.ofReal (f x) ∂(S₀.μ r)) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) :=
  markovTCBM_invariant_law_of_forall_revuz_identification h10 fun γ hγ0 hγ2 S₀ hS₀ _ _ _ =>
    ae_forall_revuz_eq_of_ratRectTent hS₀ fun i =>
      hT γ hγ0 hγ2 S₀ hS₀ (ratRectTent i) (continuous_ratRectTent i) (hasCompactSupport_ratRectTent i)
        fun w => ratRectTent_nonneg i w

end MatedCRT
