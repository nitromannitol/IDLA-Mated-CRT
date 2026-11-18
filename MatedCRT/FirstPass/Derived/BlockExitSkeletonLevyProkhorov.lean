import MatedCRT.FirstPass.Derived.BlockExitSkeletonAssembly
import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov

/-!
# From the all-sets comparison of stopped paths to the Lévy–Prokhorov distance of stopped curves

The converse of `StopAtExitLevyProkhorov.allSet_stopAtExit_le_of_levyProkhorovEDist`.

* `levyProkhorovEDist_stoppedExitCurve_le_of_allSet`: if the probability that a random continuous path
  `W`, stopped at its exit time from `U`, lies in a set `S` is at most the planar Brownian probability
  (from `z`) that the path stopped at its exit time from `U` is within `κ` of `S` for the curve distance
  modulo parametrization, plus an error `E`, for every set `S` of stopped paths, then the Lévy–Prokhorov
  distance of the laws of the stopped curve classes is at most `max κ E`. Only one of the two
  inequalities of the Lévy–Prokhorov distance is needed (both measures are probability measures).
* `levyProkhorovEDist_stoppedExitCurve_le_of_transfer`: composition with the measure assembly
  `measure_stopAtExit_le_of_transfer` of the block-exit skeleton comparison, conditional on the
  transfer bound `hTrans` for every set.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.StopAtExitCurveClass
open MatedCRT.StopAtExitLevyProkhorov

/-- **All-sets comparison of stopped paths implies a Lévy–Prokhorov bound on stopped curves.** -/
theorem levyProkhorovEDist_stoppedExitCurve_le_of_allSet {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (W : Ω → ContinuousPath ℂ) (V : Set ℂ)
    (hF : AEMeasurable (fun w => stoppedExitCurve V (W w)) ν)
    (hfin : ∀ᵐ w ∂ν, pathExitTime V ⇑(W w) ≠ ⊤) (U : Set ℂ) (hU : IsOpen U) (z : ℂ)
    (hfinB : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z), pathExitTime U ⇑b ≠ ⊤)
    {κ : ℝ} {E : ℝ≥0∞}
    (hS : ∀ S : Set (ℝ≥0 → ℂ), ν {w | stopAtExit V ⇑(W w) ∈ S} ≤
      planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ f ∈ S, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} + E) :
    levyProkhorovEDist (ν.map fun w => stoppedExitCurve V (W w))
      ((planarBrownianMotion z).map (stoppedExitCurve U)) ≤ max (ENNReal.ofReal κ) E := by
  classical
  set F : Ω → BouRabeeGwynne.CurveSpace 2 := fun w => stoppedExitCurve V (W w) with hFdef
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε hεtop hB
  have hκε : ENNReal.ofReal κ < ε := lt_of_le_of_lt (le_max_left _ _) hε
  have hEε : E ≤ ε := (le_max_right _ _).trans hε.le
  set S : Set (ℝ≥0 → ℂ) :=
    {f | ∃ w, pathExitTime V ⇑(W w) ≠ ⊤ ∧ stopAtExit V ⇑(W w) = f ∧ F w ∈ B} with hSdef
  have h1 : (ν.map F) B ≤ ν {w | stopAtExit V ⇑(W w) ∈ S} := by
    rw [Measure.map_apply_of_aemeasurable hF hB]
    refine measure_mono_ae ?_
    filter_upwards [hfin] with w hw hwB
    exact ⟨w, hw, rfl, hwB⟩
  have h2 := hS S
  have h3 : planarBrownianMotion z
      {b : ContinuousPath ℂ | ∃ f ∈ S, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal κ} ≤
      (planarBrownianMotion z).map (stoppedExitCurve U) (thickening ε.toReal B) := by
    rw [Measure.map_apply (measurable_stoppedExitCurve U hU) isOpen_thickening.measurableSet]
    refine measure_mono_ae ?_
    filter_upwards [hfinB] with b hb hmem
    obtain ⟨f, ⟨w, hw, hwf, hwB⟩, hlt⟩ := hmem
    have hc : cmpEDist (stopAtExit U ⇑b) (stopAtExit V ⇑(W w)) =
        edist (stoppedExitCurve U b) (stoppedExitCurve V (W w)) :=
      cmpEDist_stopAtExit_eq_edist_normalizedPrefixCurve U V b (W w) hb hw
    rw [← hwf, hc] at hlt
    refine (mem_thickening_iff_exists_edist_lt _ _).2 ⟨F w, hwB, ?_⟩
    rw [ENNReal.ofReal_toReal hεtop.ne]
    exact hlt.trans hκε
  exact h1.trans (h2.trans (add_le_add h3 hEε))

/-- **Lévy–Prokhorov bound for the stopped curve classes, from the block-exit skeleton comparison.**
The walk paths `W` and the planar Brownian motion from `z` stopped at their exit time from the open set
`U` have Lévy–Prokhorov distance at most `max κ (e + 2 μ G₁ᶜ + 2 ν G₂ᶜ)` provided the transfer bound
`hTrans` holds for every set `A₀` of stopped paths (see `measure_stopAtExit_le_of_transfer`). -/
theorem levyProkhorovEDist_stoppedExitCurve_le_of_transfer {Ω₁ : Type*} [MeasurableSpace Ω₁]
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (W : Ω₁ → ContinuousPath ℂ) {U : Set ℂ}
    (hF : AEMeasurable (fun w => stoppedExitCurve U (W w)) μ)
    (hfin : ∀ᵐ w ∂μ, pathExitTime U ⇑(W w) ≠ ⊤) (hU : IsOpen U) (z : ℂ)
    (hfinB : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z), pathExitTime U ⇑b ≠ ⊤)
    {s : ℝ} (hs : 0 < s) {T η : ℝ≥0}
    {d d' ε κ δ e a a' : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ}
    (hεκ : 2 * ε < κ) (hκ : 0 < κ) (hr : a' + δ + a ≤ min ε d')
    (hTrans : ∀ A₀ : Set (ℝ≥0 → ℂ),
      μ ((fun ω => blockStopped s (farSet U d') N (W ω)) ⁻¹' stopPreimage U A₀) ≤
        planarBrownianMotion z {ω : ContinuousPath ℂ | ∃ f ∈ stopPreimage U A₀,
            cmpEDist (blockStopped s (farSet U d') N ω) f < ENNReal.ofReal (a' + δ + a)} +
          ENNReal.ofReal e +
          μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}ᶜ +
          planarBrownianMotion z
            {ω : ContinuousPath ℂ | (∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') ∧
              GoodStop U T η d ε ω}ᶜ) :
    levyProkhorovEDist (μ.map fun w => stoppedExitCurve U (W w))
      ((planarBrownianMotion z).map (stoppedExitCurve U)) ≤
      max (ENNReal.ofReal κ)
        (ENNReal.ofReal e +
          2 * μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}ᶜ +
          2 * planarBrownianMotion z
            {ω : ContinuousPath ℂ | (∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') ∧
              GoodStop U T η d ε ω}ᶜ) := by
  refine levyProkhorovEDist_stoppedExitCurve_le_of_allSet μ W U hF hfin U hU z hfinB
    (fun S => ?_)
  exact le_of_le_of_eq (measure_stopAtExit_le_of_transfer μ (planarBrownianMotion z) W (fun b => b)
    hs hη hd' hdd hεκ hκ hr S (hTrans S)) (by simp only [add_assoc])

end BlockExit

end MatedCRT
