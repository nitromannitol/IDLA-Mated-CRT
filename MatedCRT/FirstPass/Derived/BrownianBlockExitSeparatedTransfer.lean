import MatedCRT.FirstPass.Derived.BrownianBlockExitTightness
import LatticeProb.Prob.KernelProkhorovChain

/-!
# Transfer of the separated-chain bound along a one-sided Prokhorov comparison

`BrownianBlockExitTightness` bounds, under the law of the block-exit positions of planar Brownian
motion, the mass of the set `separatedHistories N c K` of histories whose first `N` steps are
`c`-separated with positions in `K`. A law `μ` on histories that is one-sided Prokhorov close to
that law (`ProkhorovLE μ ν R e`: `μ A ≤ ν (thickening R A) + e` for measurable `A`) inherits the
bound: thickening by `R` turns `c`-separated histories with positions in `K` into
`(c - 2 R)`-separated histories with positions in the `R`-thickening of `K`. This is the form in
which the Brownian half of the tightness of the number of steps (step T4 of the chaining in the
proof of Theorem 3.10 of the Gwynne-Miller-Sheffield invariance principle) passes to a discrete
chain compared with the Brownian block-exit chain.

## Main results

* `thickening_separatedHistories_subset`: the deterministic inclusion.
* `separatedHistories_le_of_prokhorovLE`: the transferred superpolynomial bound.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- Thickening by `R` a set of `c`-separated histories with positions in `K` gives histories that
are `(c - 2 R)`-separated with positions in the `R`-thickening of `K`. -/
theorem thickening_separatedHistories_subset (N : ℕ) (c R : ℝ) (K : Set ℂ) :
    thickening R (separatedHistories N c K) ⊆
      separatedHistories N (c - 2 * R) (thickening R K) := by
  intro g hg
  obtain ⟨h, hh, hgh⟩ := mem_thickening_iff.1 hg
  have hd : ∀ i, ‖g i - h i‖ < R := fun i => by
    rw [← dist_eq_norm]
    exact (dist_le_pi_dist g h i).trans_lt hgh
  intro n
  obtain ⟨hsep, hK⟩ := hh n
  refine ⟨?_, mem_thickening_iff.2 ⟨h n.castSucc, hK, by rw [dist_eq_norm]; exact hd _⟩⟩
  have h1 := hd n.succ
  have h2 := hd n.castSucc
  have e1 := norm_add_le ((g n.succ - g n.castSucc) - (g n.succ - h n.succ))
    (g n.castSucc - h n.castSucc)
  have e2 := norm_sub_le (g n.succ - g n.castSucc) (g n.succ - h n.succ)
  have e3 : (g n.succ - g n.castSucc) - (g n.succ - h n.succ) + (g n.castSucc - h n.castSucc) =
      h n.succ - h n.castSucc := by ring
  rw [e3] at e1
  linarith

/-- **Transferred tightness of the number of steps.** For `0 < ζ < 1` and every `p` there is `C`
such that, with `N = ⌊r ^ (-(2 + ζ))⌋`, every law `μ` on histories with
`ProkhorovLE μ ((planarBrownianMotion z).map (blockExitPositions s F N)) R e` gives mass at most
`C r ^ p + e` to the histories whose first `N` steps are `c`-separated with positions in `K`,
whenever `0 < r < 1`, `2 a r ≤ c - 2 R` and every point of `K` is at distance less than
`a - 4 s - R` from `z`. -/
theorem separatedHistories_le_of_prokhorovLE {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ (F K : Set ℂ), MeasurableSet F → MeasurableSet K →
      ∀ (a c r R e : ℝ), 0 < a → 0 < r → r < 1 → 2 * (a * r) ≤ c - 2 * R →
      (∀ y ∈ K, ‖y - z‖ + R < a - 4 * s) →
      ∀ μ : Measure (Fin (⌊r ^ (-(2 + ζ))⌋₊ + 1) → ℂ),
      ProkhorovLE μ ((planarBrownianMotion z).map (blockExitPositions s F ⌊r ^ (-(2 + ζ))⌋₊))
        R e →
      μ (separatedHistories ⌊r ^ (-(2 + ζ))⌋₊ c K) ≤
        ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal e := by
  obtain ⟨C, hC⟩ := map_blockExitPositions_separated_superpoly hζ0 hζ1 p
  refine ⟨C, fun z s hs F K hF hK a c r R e ha hr0 hr1 hac hKz μ hP => ?_⟩
  have hK' : ∀ y ∈ thickening R K, ‖y - z‖ < a - 4 * s := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.1 hy
    have hx' := hKz x hx
    have htri := norm_sub_le_norm_sub_add_norm_sub y x z
    rw [dist_eq_norm] at hxy
    linarith
  have h1 := hP _ (measurableSet_separatedHistories ⌊r ^ (-(2 + ζ))⌋₊ c hK)
  have h2 := (measure_mono (μ := (planarBrownianMotion z).map
      (blockExitPositions s F ⌊r ^ (-(2 + ζ))⌋₊))
    (thickening_separatedHistories_subset _ c R K)).trans
    (hC z s hs F (thickening R K) hF isOpen_thickening.measurableSet a (c - 2 * R) r ha hr0 hr1
      hac hK')
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr

end BlockExit

end MatedCRT
