import MatedCRT.FirstPass.Derived.BlockExitWalkUnbounded
import MatedCRT.FirstPass.Derived.BrownianBlockExitWalkSeparated

/-!
# The walk's block-exit chain reaches the frozen set

Let the law of the first `N + 1` block-exit positions of the interpolated walk be a history chain
started at `z` whose one-step laws charge only the grid lines and are within `(δ, δ)` of the frozen
grid-rectangle block-exit kernel in the one-sided Lévy-Prokhorov sense. Along the walk, consecutive
block-exit positions off the frozen set `F` are more than `s / 2` apart almost surely
(`BlockExitWalkUnbounded`), and the separated histories have small chain mass
(`chainSeqLaw_separatedHistories_le`). Hence the walk probability that the first
`N = ⌊r ^ (-(2 + ζ))⌋` block-exit positions all avoid `F` is at most
`C r ^ p + N δ + 60 N³ δ / s`, provided every point off `F` is close to `z`.

## Main result

* `srwLaw_blockExit_avoid_frozen_le_of_chain`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess Filter
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- **The walk's block-exit chain reaches the frozen set.** For `0 < ζ < 1` and every `p` there is
`C` such that the following holds. Let `m` be a locally finite multigraph whose consecutive vertices
are adjacent, `ε > 0`, `η` a continuous proper curve, `c > 0` a speed, `F` a measurable frozen set and
`z` a point of the open grid rectangle. Suppose every point off `F` lies at distance less than
`a - 4 s - (N + 1) δ` from `z`, and that the law under `srwLaw m x₀` of the first `N + 1` block-exit
positions of the interpolated walk is the history chain started at `z` with one-step laws `q n`
charging only the grid lines and within `(δ, δ)` of the frozen grid-rectangle block-exit kernel.
Then the probability that the first `N = ⌊r ^ (-(2 + ζ))⌋` block-exit positions all avoid `F` is at
most `C r ^ p + N δ + 60 N³ δ / s`. -/
theorem srwLaw_blockExit_avoid_frozen_le_of_chain {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m → (∀ k : ℤ, m k (k + 1) ≠ 0) →
      ∀ (ε : ℝ), 0 < ε → ∀ (η : ℝ → ℂ), Continuous η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ (c : ℝ) (hc : 0 < c) (x₀ : ℤ) (s : ℝ), 0 < s → ∀ (a₁ a₂ c₁ c₂ : ℤ) (z : ℂ),
      z ∈ gridRectOpen s a₁ a₂ c₁ c₂ → ∀ (F : Set ℂ), MeasurableSet F →
      ∀ (a r δ : ℝ) (N : ℕ), N = ⌊r ^ (-(2 + ζ))⌋₊ → 0 < N → 0 < a → 0 < r → r < 1 →
      0 < δ → ((N : ℝ) + 1) * δ ≤ s / 4 → 2 * (a * r) ≤ s / 2 - 2 * (((N : ℝ) + 1) * δ) →
      (∀ y ∉ F, ‖y - z‖ + ((N : ℝ) + 1) * δ < a - 4 * s) →
      ∀ (q : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ), (∀ n, Measurable (q n)) →
      (∀ n g, IsProbabilityMeasure (q n g)) →
      (∀ n < N, ∀ g, q n g (gridLines s)ᶜ = 0) →
      (∀ n < N, ∀ g, ProkhorovLE (q n g)
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) δ δ) →
      (srwLaw m x₀).map
          (fun x => blockExitPositions s F N (interpPathCM (vertexPoint ε η) hc.le x)) =
        chainSeqLaw (fun n => paddedHistoryKernel n (q n)) (Measure.dirac fun _ => z) N →
      srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F} ≤
        ENNReal.ofReal (C * r ^ p) +
          ENNReal.ofReal (N * δ + 60 * (N : ℝ) ^ 3 * δ / s) := by
  obtain ⟨C, hC⟩ := chainSeqLaw_separatedHistories_le hζ0 hζ1 p
  refine ⟨C, fun m hlf hcons ε hε η hη hp c hc x₀ s hs a₁ a₂ c₁ c₂ z hz F hF a r δ N hNr hN ha
    hr0 hr1 hδ hδs hac hKz q hq hqP hqΓ hqK hlaw => ?_⟩
  have hH : Measurable
      (fun x => blockExitPositions s F N (interpPathCM (vertexPoint ε η) hc.le x)) :=
    (measurable_blockExitPositions s hF N).comp (measurable_interpPathCM _ hc.le)
  calc srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F}
      ≤ srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F ∧
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∈ Fᶜ} :=
        measure_mono fun x hx n hn => ⟨hx n hn, hx n hn⟩
    _ ≤ srwLaw m x₀ ((fun x => blockExitPositions s F N
          (interpPathCM (vertexPoint ε η) hc.le x)) ⁻¹' separatedHistories N (s / 2) Fᶜ) :=
        srwLaw_blockExit_avoid_le_separatedHistories hlf hcons hε hη hp hc x₀ hs F Fᶜ N
    _ = chainSeqLaw (fun n => paddedHistoryKernel n (q n)) (Measure.dirac fun _ => z) N
          (separatedHistories N (s / 2) Fᶜ) := by
        rw [← hlaw, Measure.map_apply hH (measurableSet_separatedHistories N _ hF.compl)]
    _ ≤ _ := hC s hs a₁ a₂ c₁ c₂ z hz Fᶜ hF.compl a (s / 2) r δ N hNr hN ha hr0 hr1 hδ hδs hac
        hKz q hq hqP hqΓ hqK

end BlockExit

end MatedCRT
