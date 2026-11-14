import MatedCRT.FirstPass.Derived.LevyProkhorovWeakFiniteMeasure
import MatedCRT.FirstPass.Derived.DegreeCutoffLevyProkhorov
import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import LatticeProb.Prob.ConvergingTogetherProjection
import LatticeProb.Prob.ProbabilityMeasureSeparable

/-!
# The walk-side tuple converges in law (Berestycki–Gwynne, proof of Lemma 7.6)

Let `S` be a valid mated-CRT environment with LQG measure `μ_h`, `η'` a measurable version of its
space-filling SLE curve, `ψ ≥ 0` continuous with compact support and `ε_n → 0+`. Let
`ψ ν^{ε_n}` be the degree measure of the mated-CRT map cut off by `ψ` (`degreeCutoffMeasure`) and
`P̃^{ε_n}` the interpolated quenched law of the embedded random walk (`interpWalkLaw`). Suppose that
`(D_n, P̃^{ε_n})` converges in law to `ν`, where `D_n` is random data with a continuous projection
`π` to finite measures which almost surely equals `6 ψ μ_h` (the measure `μ_h` is a coordinate of the
data, so neither the Skorokhod representation nor Lusin's theorem is needed). Then, for times
`t_n → s₀`,
`(ψ ν^{ε_n}, P̃^{ε_n}, t_n) → (π d, P, s₀)` in law, `(d, P)` distributed according to `ν`,
the measure coordinate carrying the topology of weak convergence of finite measures.

The proof is the converging-together lemma with a projected coordinate
(`LatticeProb.tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`),
fed with the Lévy–Prokhorov convergence in probability `ψ ν^{ε_n} - 6 ψ μ_h → 0`
(`tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection`, from the degree measure
convergence of Theorem 2.7 and the vanishing of the cell diameters, `hdiam_of_isValid`), followed by
the continuity of the identity from the Lévy–Prokhorov metric to the weak topology on finite
measures (`MatedCRT.continuous_levyProkhorov_toFiniteMeasure`).

## Main results

* `aemeasurable_reversibilityLimitLaw_state`: the random element
  `(ψ ν^{ε_n}, P̃^{ε_n}, t_n)` of `FiniteMeasure ℂ × C(ℂ, Prob(C(ℝ≥0, ℂ))) × ℝ≥0` is almost
  everywhere measurable for the Borel `σ`-algebra.
* `tendsto_integral_reversibilityLimitLaw`: the convergence in law above, in the form of the
  hypothesis `hlaw` of `LatticeProb.ae_reversibilityPairing_eq_zero_of_tendsto_law`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set LatticeProb
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The walk-side state is a random element.** For a valid environment, a measurable version `η'`
of the curve, a measurable `ψ` with compact support and `ε_n > 0`, the state
`(ψ ν^{ε_n}, P̃^{ε_n}, t_n)` is almost everywhere measurable for the Borel `σ`-algebra of
`FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0` (the hypothesis `hW` of
`LatticeProb.ae_reversibilityPairing_eq_zero_of_tendsto_law`). -/
theorem aemeasurable_reversibilityLimitLaw_state
    [MeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    [BorelSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Measurable ψ) (hψc : HasCompactSupport ψ) {ε : ℕ → ℝ}
    (hε0 : ∀ n, 0 < ε n) (t : ℕ → ℝ≥0) :
    ∀ n, AEMeasurable (fun ω =>
      ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ,
        interpWalkLaw S η' (ε n) ω, t n) :
          FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)) S.P := by
  intro n
  let : MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ)) := borel _
  have : BorelSpace (LevyProkhorov (FiniteMeasure ℂ)) := ⟨rfl⟩
  have hpair : AEMeasurable (fun ω =>
      (LevyProkhorov.ofMeasure
          (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ),
        ((interpWalkLaw S η' (ε n) ω : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))), t n))) S.P :=
    (hμ_degreeCutoffMeasure_of_isValid hS hae hψ hψc hε0 n).prodMk
      ((aemeasurable_interpWalkLaw hS hη' hae (hε0 n)).prodMk aemeasurable_const)
  have hΦ : Continuous fun x : LevyProkhorov (FiniteMeasure ℂ) ×
      C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 =>
      ((x.1.toMeasure, x.2) : FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) :=
    (continuous_levyProkhorov_toFiniteMeasure.comp continuous_fst).prodMk continuous_snd
  exact hΦ.measurable.comp_aemeasurable hpair

/-- **The walk-side tuple converges in law** (Berestycki–Gwynne, proof of Lemma 7.6). Let `S` be a
valid environment, `η'` a measurable version of its curve, `ψ ≥ 0` continuous with compact support,
`ε_n → 0+` and `t_n → s₀`. Let `D_n` be random data in a pseudo-metrizable second countable space
with a projection `π` to finite measures, continuous for the Lévy–Prokhorov metric, such that
`π (D_n) = 6 ψ μ_h` almost surely, and suppose that `(D_n, P̃^{ε_n}) → ν` in law. Given the degree
measure convergence of Theorem 2.7 (`hD27`), the state `(ψ ν^{ε_n}, P̃^{ε_n}, t_n)` converges in law
to the image of `ν` under `(d, P) ↦ (π d, P, s₀)`, for the Borel `σ`-algebra and the topology of weak
convergence on the finite measure coordinate. -/
theorem tendsto_integral_reversibilityLimitLaw
    [MeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    [BorelSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {s₀ : ℝ≥0} (ht : Tendsto t atTop (𝓝 s₀))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {π : X → FiniteMeasure ℂ} (hπ : Continuous fun d => LevyProkhorov.ofMeasure (π d))
    (hπD : ∀ n, ∀ᵐ ω ∂S.P,
      (π (D n ω) : Measure ℂ) = (S.μ ω).withDensity fun z => ENNReal.ofReal (6 * ψ z))
    {ν : Measure (X × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
        (𝓝 (∫ p, F p ∂ν))) :
    ∀ F : (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω,
          F (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ,
            interpWalkLaw S η' (ε n) ω, t n) ∂S.P) atTop
        (𝓝 (∫ w, F w ∂(ν.map fun p => (π p.1, p.2, s₀)))) := by
  let : MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ)) := borel _
  have : BorelSpace (LevyProkhorov (FiniteMeasure ℂ)) := ⟨rfl⟩
  have := hS.isProbabilityMeasure
  have hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun ε => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R}) (𝓝[>] 0)
        (𝓝 0) := by
    intro R a ha
    rw [tendsto_iff_seq_tendsto]
    intro x hx
    exact hdiam_of_isValid hS hae (hx.mono_right nhdsWithin_le_nhds) R a ha
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => Set.mem_Ioi.2 (hε0 n)⟩
  have hμπ := tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection hγ hγ2 hS hD27
    hae hψ hψc hψ0 hdiam hεw hπD
  have hCT := tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist
    hD (hμ_degreeCutoffMeasure_of_isValid hS hae hψ.measurable hψc hε0)
    (fun n => aemeasurable_interpWalkLaw hS hη' hae (hε0 n)) hπ hlaw hμπ ht
  intro F
  have hΦ : Continuous fun x : X × LevyProkhorov (FiniteMeasure ℂ) ×
      C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 =>
      ((x.2.1.toMeasure, x.2.2.1, x.2.2.2) :
        FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) :=
    (continuous_levyProkhorov_toFiniteMeasure.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have hg : Continuous fun p : X × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) =>
      ((π p.1, p.2, s₀) : FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) :=
    ((continuous_levyProkhorov_toFiniteMeasure.comp hπ).comp continuous_fst).prodMk
      (continuous_snd.prodMk continuous_const)
  rw [integral_map hg.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact hCT (F.compContinuous ⟨_, hΦ⟩)

end MatedCRT.FirstPass.Derived
