import MatedCRT.FirstPass.Derived.LQGMeasureNeZeroWiring
import MatedCRT.FirstPass.Derived.MarkovTimeChange

/-!
# The Markov and nondegeneracy premise for the identification of the limiting walk laws

The identification of subsequential limits of the interpolated walk laws with the law of Liouville Brownian motion
(BG20, §7.3) uses, for a valid environment and measurable data `(pairJ ⊤ H, E)` whose coordinate `μX (E ω)` is almost
surely the LQG measure `μ_h`, the premise that for almost every value `d` of the data:

1. the law field `lbmPathLawField γ d.1` of the rescaled Liouville Brownian motion is a Markovian time change of
   Brownian motion (Definitions 7.1 and 7.2, `IsMarkovTCBM`);
2. the measure `μX d.2` is invariant for it (Definition 7.3, `IsInvariantFor`);
3. `μX d.2 ≠ 0`;
4. the median of the exit time from `B_{1/2}` under `lbmPathLawField γ d.1 0` is nonzero.

* `hN8_of_isMarkovTCBM_isInvariantFor`: the last two items hold for every valid environment, so the premise follows
  from its first two items alone. Item 3 comes from `ae_map_pairJ_ne_zero_of_isValid` (the curve is parametrized by
  `μ_h`-area, and `{d | μX d ≠ 0}` is Borel when the cutoff measures `ψ μX d` are Lévy–Prokhorov continuous in
  `d`), item 4 from `ae_medianOf_exitCdf_lbmPathLawField_ne_zero` (the exit time of the rescaled Liouville Brownian
  motion from `B_{1/2}` is almost surely positive and finite).
-/

open MeasureTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The Markov and nondegeneracy premise from the Markov time change and the invariance alone.** Let `μX` be a
family of locally finite measures on the plane indexed by a topological space `M` with its Borel σ-algebra, with `d ↦ ψ μX d` Lévy–Prokhorov
continuous for every nonnegative continuous compactly supported cutoff `ψ`. Suppose that for every valid
environment at `0 < γ < 2`, every measurable version `H` of its field and all measurable data `E` with
`μX (E ω) = μ_h` almost surely, for almost every `d` under the law of `(pairJ ⊤ H, E)` the law field
`lbmPathLawField γ d.1` is a Markovian time change of Brownian motion with `μX d.2` invariant. Then, in addition,
`μX d.2 ≠ 0` and the median of the exit time from `B_{1/2}` under `lbmPathLawField γ d.1 0` is nonzero for almost
every such `d`. -/
theorem hN8_of_isMarkovTCBM_isInvariantFor {𝒮 : SpaceFillingSLEModel} {M : Type} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] (μX : M → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    (hN8' :
      ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → (∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (μX d.2)) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → M, Measurable E → (∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (μX d.2) ∧
          μX d.2 ≠ 0 ∧ medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2))
            (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))) ≠ 0 := by
  intro γ hγ hγ2 Ω _ S hS H hH hrep E hE hEμ
  filter_upwards [hN8' γ hγ hγ2 Ω S hS H hH hrep E hE hEμ,
    ae_map_pairJ_ne_zero_of_isValid hS hH hE μX hπ hEμ,
    ae_medianOf_exitCdf_lbmPathLawField_ne_zero hγ hγ2 hS hH hrep hE] with d h1 h2 h3
  exact ⟨h1.1, h1.2, h2, h3⟩

end MatedCRT.FirstPass.Derived
