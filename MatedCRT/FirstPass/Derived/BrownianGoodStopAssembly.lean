import MatedCRT.FirstPass.Derived.BrownianGoodStopInside

/-!
# The good stopping event of planar Brownian motion, uniformly in the starting point of a disc

The three clauses of `MatedCRT.StopAtExitCmp.GoodStop (ball 0 R) T η d ε` hold with probability close to one for
planar Brownian motion started at any point of `closedBall 0 ρ`, `ρ < R`, with ONE choice of the parameters
`(T, η, d)` for given `ε`, `θ`:

* the exit-witness clause (a), `exists_forall_planarBrownianMotion_witnessBad_lt` (the horizon `T` and `d`),
* the oscillation clause (b), `exists_forall_planarBrownianMotion_oscillationBad_lt` (the scale `η`),
* the inside-ball clause (c), `exists_forall_planarBrownianMotion_insideBad_lt` (the radius `d`).

The violation sets of (a) and (c) decrease with `d`, that of (b) with `η`; a union bound with the failure
probabilities `θ / 3` gives `exists_forall_planarBrownianMotion_not_goodStop_lt`.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal
open MatedCRT.ExitRestart

namespace MatedCRT.StopAtExitCmp

/-- The violation set of the exit-witness clause decreases as `d` decreases. -/
theorem witnessBad_anti {R : ℝ} {T η : ℝ≥0} {d d' : ℝ} (h : d' ≤ d) :
    witnessBad R T η d' ⊆ witnessBad R T η d := by
  intro b hb hgood
  obtain ⟨q, h1, h2, h3, h4⟩ := hgood
  exact hb ⟨q, h1, h2, h3, fun w hw => h4 w (lt_of_lt_of_le hw h)⟩

/-- The violation set of the inside-ball clause decreases as `d` decreases. -/
theorem insideBad_anti {R : ℝ} {η : ℝ≥0} {d d' : ℝ} (h : d' ≤ d) :
    insideBad R η d' ⊆ insideBad R η d := by
  intro b hb hgood
  exact hb fun q hq w hw => hgood q hq w (lt_of_lt_of_le hw h)

/-- **The good stopping event of planar Brownian motion, uniformly in the start.** For `0 ≤ ρ < R`, `ε > 0` and
`θ > 0` there are a horizon `T`, a scale `η > 0` and a radius `d > 0` such that planar Brownian motion started
at every point of `closedBall 0 ρ` violates `GoodStop (ball 0 R) T η d ε` with probability less than `θ`. -/
theorem exists_forall_planarBrownianMotion_not_goodStop_lt {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ T η : ℝ≥0, 0 < η ∧ ∃ d : ℝ, 0 < d ∧ ∀ z ∈ closedBall (0 : ℂ) ρ,
      planarBrownianMotion z {b : ContinuousPath ℂ | ¬ GoodStop (ball (0 : ℂ) R) T η d ε ⇑b} <
        ENNReal.ofReal θ := by
  have hθ3 : 0 < θ / 3 := by positivity
  obtain ⟨T, -, hTa⟩ := exists_forall_planarBrownianMotion_witnessBad_lt hρ hρR hθ3
  obtain ⟨η₀, hη₀, hosc⟩ := exists_forall_planarBrownianMotion_oscillationBad_lt T hε hθ3
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ≥0, η = min η₀ 1 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hηdef]; exact lt_min hη₀ one_pos
  have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_right _ _
  have hηη₀ : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
  obtain ⟨da, hda, hwit⟩ := hTa η hηpos hη1
  obtain ⟨dc, hdc, -, hins⟩ := exists_forall_planarBrownianMotion_insideBad_lt hρ hρR hθ3 hηpos
  refine ⟨T, η, hηpos, min da dc, lt_min hda hdc, fun z hz => ?_⟩
  have hsub : {b : ContinuousPath ℂ | ¬ GoodStop (ball (0 : ℂ) R) T η (min da dc) ε ⇑b} ⊆
      witnessBad R T η da ∪ (oscillationBad T η₀ ε ∪ insideBad R η dc) := by
    intro b hb
    by_contra hcon
    rw [mem_union, mem_union, not_or, not_or] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hb' : ¬ GoodStop (ball (0 : ℂ) R) T η (min da dc) ε ⇑b := hb
    apply hb'
    unfold GoodStop
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      have hm : b ∈ witnessBad R T η (min da dc) := h
      exact h1 (witnessBad_anti (min_le_left da dc) hm)
    · by_contra h
      have hm : b ∈ oscillationBad T η ε := h
      exact h2 (oscillationBad_anti ε hηη₀ hm)
    · by_contra h
      have hm : b ∈ insideBad R η (min da dc) := h
      exact h3 (insideBad_anti (min_le_right da dc) hm)
  have h3 : ENNReal.ofReal (θ / 3) + (ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3)) =
      ENNReal.ofReal θ := by
    have h0 : 0 ≤ θ / 3 := hθ3.le
    rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add h0 (by positivity)]
    congr 1
    ring
  calc planarBrownianMotion z {b : ContinuousPath ℂ | ¬ GoodStop (ball (0 : ℂ) R) T η (min da dc) ε ⇑b}
      ≤ planarBrownianMotion z (witnessBad R T η da ∪ (oscillationBad T η₀ ε ∪ insideBad R η dc)) :=
        measure_mono hsub
    _ ≤ planarBrownianMotion z (witnessBad R T η da) +
          (planarBrownianMotion z (oscillationBad T η₀ ε) + planarBrownianMotion z (insideBad R η dc)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ < ENNReal.ofReal (θ / 3) + (ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3)) :=
        ENNReal.add_lt_add (hwit z hz) (ENNReal.add_lt_add (hosc z) (hins z hz))
    _ = ENNReal.ofReal θ := h3

end MatedCRT.StopAtExitCmp
