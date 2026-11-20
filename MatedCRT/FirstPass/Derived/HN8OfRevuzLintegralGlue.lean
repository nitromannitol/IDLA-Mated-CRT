import MatedCRT.FirstPass.Derived.HN8OfRevuzTestIdentity
import MatedCRT.FirstPass.Derived.OccupationBallLawAssembly
import MatedCRT.FirstPass.Derived.ValidApproximantBallBound
import MatedCRT.FirstPass.Derived.HN5Discharged

/-!
# The Revuz measure of the Liouville clock of a valid environment, integrated against a test function

For a valid environment `S` (`MatedCRTEnv.IsValid`) and every nonnegative continuous compactly supported
`f : ℂ → ℝ`, almost surely every PCAF version `G` of the Liouville clock of `S`
(`G t b = S.clock ω b t` for almost every planar Brownian path from every start) satisfies
`∫⁻ ofReal f d(revuz planarLaw G) = ∫⁻ ofReal f d(S.μ ω)`.  This is
`lintegral_ofReal_revuz_eq_of_lqgClock` applied to the fields of `IsValid`:
`isLQGMeasure` (the limit of the circle-average approximants), `isLQGClock`, the almost sure continuity of the
dyadic circle averages (`IsQuantumCone.ae_continuousOn_circle`), and the almost sure power ball-mass bound of the
approximants (`ae_approximant_ballBound_of_isValid`), which is applied on the ball of radius `n + 1`, `n` bounding
the support of `f`.  It feeds the per-test-function identity hypothesis of
`markovTCBM_invariant_law_of_forall_revuz_lintegral_identification`, which then gives `hN8'` as typed from the
reference environments of the model (`hN8'_of_hasReferenceEnvironments`), and with it `hN8'` leaves the premises of
`randomWalkToLBMStmt_of_markovLimit_derived_noHN5` (`randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8`).
-/

namespace MatedCRT

open MeasureTheory MarkovProcess Set Filter Topology Metric
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}

/-- A continuous compactly supported function is bounded and vanishes outside a ball. -/
theorem exists_bound_and_norm_of_continuous_hasCompactSupport {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ K n : ℝ, 0 ≤ n ∧ (∀ x, f x ≤ K) ∧ ∀ x : ℂ, n < ‖x‖ → f x = 0 := by
  obtain ⟨K, hK⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨K, max r 0, le_max_right _ _, fun x => (le_abs_self _).trans (hK x), fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := mem_closedBall_zero_iff.1 (hr hmem)
  exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left r 0) hx)) (lt_irrefl _)

/-- **The Revuz measure of the Liouville clock of a valid environment, against test functions.**  For
`γ ∈ (0, 2)`, a valid environment `S` and a nonnegative continuous compactly supported `f`, almost surely, for
every PCAF version `G` of the clock of `S`, the integral of `f` against the Revuz measure of `G` is its integral
against the LQG measure `S.μ ω`. -/
theorem ae_lintegral_revuz_eq_of_isValid (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : 0 ≤ f) :
    ∀ᵐ ω ∂S.P, ∀ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G →
      (∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t) →
      ∫⁻ x, ENNReal.ofReal (f x) ∂(revuz planarLaw G) = ∫⁻ x, ENNReal.ofReal (f x) ∂(S.μ ω) := by
  obtain ⟨K, n, hn0, hfK, hfn⟩ := exists_bound_and_norm_of_continuous_hasCompactSupport hf hfc
  filter_upwards [hS.isLQGMeasure, hS.isLQGClock, FirstPass.Derived.ae_approximant_ballBound_of_isValid hγ hγ2 hS,
    hS.isQuantumCone.ae_continuousOn_circle] with ω hμ hclk hb hcont G hG hGF
  obtain ⟨β, C, hβ, hC, hball⟩ := hb (n + 1) (by linarith)
  have hk : ∀ k : ℕ, Continuous (S.hcirc ω (_root_.HarmonicBalls.dyadicScale k)) := fun k => by
    apply continuousOn_univ.mp
    apply hcont.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    refine ⟨?_, mem_univ z⟩
    show (0 : ℝ) < (2 : ℝ)⁻¹ ^ k
    positivity
  exact FirstPass.Derived.lintegral_ofReal_revuz_eq_of_lqgClock ((_root_.HarmonicBalls.LPBridge.isLQGLimit_iff _ _ _).1 hμ) hk (fun z => (hclk z).1) hG hGF hβ hC
    (fun z hz r hr0 hr1 k => hball z hz r hr0 hr1 k) hf (fun x => ⟨hf0 x, hfK x⟩) hfn

end ValidEnvironment

/-- **`hN8'` from the reference environments.**  Given the reference environments of the model (`h10`), the Liouville
Brownian motion path law field of every valid environment is almost surely a Markov time change of Brownian motion
that is invariant for the LQG measure, as typed in `randomWalkToLBMStmt_of_markovLimit_derived_noHN5`.  The Revuz
measure of every PCAF version of the clock is identified with the LQG measure by
`ae_lintegral_revuz_eq_of_isValid`. -/
theorem hN8'_of_hasReferenceEnvironments {𝒮 : SpaceFillingSLEModel} (h10 : HasReferenceEnvironments 𝒮) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) :=
  markovTCBM_invariant_law_of_forall_revuz_lintegral_identification h10
    fun _ hγ0 hγ2 _ hS₀ _ hf hfc hf0 =>
      (ae_lintegral_revuz_eq_of_isValid hγ0 hγ2 hS₀ hf hfc hf0).mono fun _ h G hA _ _ hGa => h G hA hGa

/-- **Lemma 7.4 and the Markov limit with `hN8'` proved.**  `randomWalkToLBMStmt_of_markovLimit_derived_noHN5`
with the premise `hN8'` replaced by its proof from `h10` (`hN8'_of_hasReferenceEnvironments`); the remaining
premises are `h1 h2 hN4 h10 hN9`. -/
theorem randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8 {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_derived_noHN5 h1 h2 hN4 h10 (hN8'_of_hasReferenceEnvironments h10) hN9

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the convergence of the embedded random walk to Liouville
Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8`: the premises `hN8'`
(Markov and invariance property of Liouville Brownian motion; proved from `h10`) and `hN5` (Berestycki-Gwynne (2020),
Lemma 7.4; proved from `hN4`) of `closed_1_4_quantumConeScaling_coneDimension_markovLimit` no longer occur. The remaining premises are
`h1 h2 hN4 h10 hN9`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8 h1 h2 hN4 h10 hN9)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the convergence of the embedded random walk to Liouville
Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8`: the premises `hN8'`
(Markov and invariance property of Liouville Brownian motion; proved from `h10`) and `hN5` (Berestycki-Gwynne (2020),
Lemma 7.4; proved from `hN4`) of `closed_1_6_quantumConeScaling_coneDimension_markovLimit` no longer occur. The remaining premises are
`h1 h2 hN4 h10 hN9`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8 h1 h2 hN4 h10 hN9)

end MatedCRT
