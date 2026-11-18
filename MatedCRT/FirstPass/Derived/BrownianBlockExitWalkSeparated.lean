import MatedCRT.FirstPass.Derived.BrownianBlockExitSeparatedTransfer
import MatedCRT.FirstPass.Derived.BrownianBlockExitChainError
import LatticeProb.Prob.KernelHistoryFirstStep

/-!
# Separated walk histories from the block-exit chain comparison

For the open grid rectangle `(a₁ s, a₂ s) × (c₁ s, c₂ s)` and the block-exit chain of planar
Brownian motion frozen off it:

* `map_blockExitPositions_gridRect_succ`: the first-step decomposition of the law of the
  block-exit positions, specialised to the frozen set `(gridRectOpen s a₁ a₂ c₁ c₂)ᶜ`, in terms
  of `gridRectBlockExitKernel`;
* `chainSeqLaw_separatedHistories_le_of_eq`: if the frozen history chain law started at `z`
  coincides with the law of the first `N + 1` block-exit positions of planar Brownian motion
  started at `z`, with `N = ⌊r ^ (-(2 + ζ))⌋₊`, then every history chain whose one-step laws are
  within `(ε, ε)` of the frozen block-exit kernel in the one-sided Lévy–Prokhorov sense and
  charge only the grid lines gives mass at most `C r ^ p + N ε + 60 N ³ ε / s` to the histories
  whose first `N` steps are `c`-separated and stay in `K`.

* `law_blockExitPositions_eq_chainHistoryLaw`: the identification of the two laws, by the
  first-step recursion of the history chain law (`eq_chainHistoryLaw_of_succ`) and
  `map_blockExitPositions_succ`;
* `chainSeqLaw_separatedHistories_le`: the separated-history bound without the identification
  hypothesis.
-/

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- First-step decomposition of the block-exit positions of planar Brownian motion frozen off
the open grid rectangle, in terms of `gridRectBlockExitKernel`. -/
theorem map_blockExitPositions_gridRect_succ (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) (N : ℕ) (z : ℂ) :
    (planarBrownianMotion z).map
        (blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ (N + 1)) =
      ((gridRectBlockExitKernel s a₁ a₂ c₁ c₂ z).bind fun x =>
        (planarBrownianMotion x).map
          (blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N)).map
        (fun g : Fin (N + 1) → ℂ => (Fin.cons z g : Fin (N + 1 + 1) → ℂ)) :=
  map_blockExitPositions_succ s (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl N z

/-- Separated histories of a chain compared with the frozen block-exit chain: once the frozen
history chain law agrees with the law of the block-exit positions of planar Brownian motion,
the one-sided Lévy–Prokhorov comparison of `prokhorovLE_chainSeqLaw_gridRectBlockExit_cubic`
transfers the superpolynomial bound on separated block-exit histories to the compared chain,
at the cost of the comparison error `N ε + 60 N ³ ε / s`. -/
theorem chainSeqLaw_separatedHistories_le_of_eq {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (s : ℝ), 0 < s → ∀ (a₁ a₂ c₁ c₂ : ℤ) (z : ℂ),
      z ∈ gridRectOpen s a₁ a₂ c₁ c₂ → ∀ (K : Set ℂ), MeasurableSet K →
      ∀ (a c r ε : ℝ) (N : ℕ), N = ⌊r ^ (-(2 + ζ))⌋₊ → 0 < N → 0 < a → 0 < r → r < 1 →
      0 < ε → ((N : ℝ) + 1) * ε ≤ s / 4 → 2 * (a * r) ≤ c - 2 * (((N : ℝ) + 1) * ε) →
      (∀ y ∈ K, ‖y - z‖ + ((N : ℝ) + 1) * ε < a - 4 * s) →
      ∀ (q : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ), (∀ n, Measurable (q n)) →
      (∀ n g, IsProbabilityMeasure (q n g)) →
      (∀ n < N, ∀ g, q n g (gridLines s)ᶜ = 0) →
      (∀ n < N, ∀ g, ProkhorovLE (q n g)
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) ε ε) →
      chainSeqLaw (fun m => paddedHistoryKernel m
          (fun g => gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))))
        (Measure.dirac fun _ => z) N =
        (planarBrownianMotion z).map
          (blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N) →
      chainSeqLaw (fun m => paddedHistoryKernel m (q m)) (Measure.dirac fun _ => z) N
          (separatedHistories N c K) ≤
        ENNReal.ofReal (C * r ^ p) +
          ENNReal.ofReal (N * ε + 60 * (N : ℝ) ^ 3 * ε / s) := by
  obtain ⟨C, hC⟩ := separatedHistories_le_of_prokhorovLE hζ0 hζ1 p
  refine ⟨C, fun s hs a₁ a₂ c₁ c₂ z hz K hK a c r ε N hNr hN ha hr0 hr1 hε hεs hac hKz q hq
    hqP hqΓ hqK hid => ?_⟩
  have hP := prokhorovLE_chainSeqLaw_gridRectBlockExit_cubic hs a₁ a₂ c₁ c₂ hN hz hε hεs
    (p := q) hq hqΓ hqK
  rw [hid] at hP
  subst hNr
  exact hC z s hs _ K (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl hK a c r _ _ ha
    hr0 hr1 hac hKz _ hP

/-- **Law of the block-exit positions**: the first `N + 1` block-exit positions of planar
Brownian motion started at `z`, with the blocks frozen on `F`, have the history law of the frozen
block-exit kernel started at `z`. -/
theorem law_blockExitPositions_eq_chainHistoryLaw (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F)
    (N : ℕ) (z : ℂ) :
    (planarBrownianMotion z).map (blockExitPositions s F N) =
      chainHistoryLaw (frozenBlockExitKernel s hF) N z := by
  have h := eq_chainHistoryLaw_of_succ (frozenBlockExitKernel s hF).measurable
    (fun N z => (planarBrownianMotion z).map (blockExitPositions s F N))
    (fun x => map_blockExitPositions_zero s F x) (fun N z => map_blockExitPositions_succ s hF N z) N
  exact congrFun h z

/-- Separated histories of a chain compared with the Brownian block-exit chain frozen off the
open grid rectangle: every history chain whose one-step laws are within `(ε, ε)` of the frozen
block-exit kernel in the one-sided Lévy–Prokhorov sense and charge only the grid lines gives mass
at most `C r ^ p + N ε + 60 N ³ ε / s` to the histories whose first `N = ⌊r ^ (-(2 + ζ))⌋₊`
steps are `c`-separated and stay in `K`. -/
theorem chainSeqLaw_separatedHistories_le {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (s : ℝ), 0 < s → ∀ (a₁ a₂ c₁ c₂ : ℤ) (z : ℂ),
      z ∈ gridRectOpen s a₁ a₂ c₁ c₂ → ∀ (K : Set ℂ), MeasurableSet K →
      ∀ (a c r ε : ℝ) (N : ℕ), N = ⌊r ^ (-(2 + ζ))⌋₊ → 0 < N → 0 < a → 0 < r → r < 1 →
      0 < ε → ((N : ℝ) + 1) * ε ≤ s / 4 → 2 * (a * r) ≤ c - 2 * (((N : ℝ) + 1) * ε) →
      (∀ y ∈ K, ‖y - z‖ + ((N : ℝ) + 1) * ε < a - 4 * s) →
      ∀ (q : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ), (∀ n, Measurable (q n)) →
      (∀ n g, IsProbabilityMeasure (q n g)) →
      (∀ n < N, ∀ g, q n g (gridLines s)ᶜ = 0) →
      (∀ n < N, ∀ g, ProkhorovLE (q n g)
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) ε ε) →
      chainSeqLaw (fun m => paddedHistoryKernel m (q m)) (Measure.dirac fun _ => z) N
          (separatedHistories N c K) ≤
        ENNReal.ofReal (C * r ^ p) +
          ENNReal.ofReal (N * ε + 60 * (N : ℝ) ^ 3 * ε / s) := by
  obtain ⟨C, hC⟩ := chainSeqLaw_separatedHistories_le_of_eq hζ0 hζ1 p
  exact ⟨C, fun s hs a₁ a₂ c₁ c₂ z hz K hK a c r ε N hNr hN ha hr0 hr1 hε hεs hac hKz q hq hqP
    hqΓ hqK => hC s hs a₁ a₂ c₁ c₂ z hz K hK a c r ε N hNr hN ha hr0 hr1 hε hεs hac hKz q hq hqP
      hqΓ hqK (law_blockExitPositions_eq_chainHistoryLaw s _ N z).symm⟩

end BlockExit

end MatedCRT
