import MatedCRT.FirstPass.Derived.BlockExitSkeletonEvents

/-!
# Measure assembly of the block-exit skeleton comparison of stopped paths

Let `W : Ω₁ → ContinuousPath ℂ` (walk paths) and `B : Ω₂ → ContinuousPath ℂ` (Brownian paths) be
two families of continuous paths with laws `μ` and `ν`. Let `s > 0`, `d' > 0`, `N : ℕ`, and write
`F = farSet U d'`, `σ_N` for the `N`-th block exit time of the chain frozen on `F`. Let
`G₁ = {ω | the chain of W ω reaches F within N steps}` and
`G₂ = {ω | the chain of B ω reaches F within N steps, and B ω is in GoodStop}`.

The one-sided transfer bound for skeleton laws (a measure-theoretic statement about curves modulo
time parametrization, applied to `P₁ = blockStopped ∘ W`, `P₂ = blockStopped ∘ B`, the step
reconstruction `Φ = stepPath N`, the skeletons `blockExitPositions`, and `A = stopPreimage U A₀`)
reads

`μ (P₁ ⁻¹' A) ≤ ν {ω | ∃ f ∈ A, cmpEDist (P₂ ω) f < a' + δ + a} + e + μ G₁ᶜ + ν G₂ᶜ`.

Together with the pointwise inclusions of `BlockExitSkeletonEvents` it gives, for every set `A₀` of
paths, the one-sided comparison of the stopped-at-exit laws

`μ {stopAtExit U (W ω) ∈ A₀} ≤ ν {∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < κ}
  + e + 2 μ G₁ᶜ + 2 ν G₂ᶜ`.

The transfer bound is an explicit hypothesis (`hTrans`) of this conditional helper.
-/

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- **Measure assembly (conditional on the transfer bound).** If `hTrans` (the one-sided transfer
bound for the skeleton laws, for `A = stopPreimage U A₀`) holds, then the law of the walk stopped at
its exit time from `U` is dominated, on every set `A₀`, by the law of the Brownian motion stopped at
its exit time, up to the `κ`-neighbourhood of `A₀`, the skeleton error `e` and the exceptional
masses of `G₁` and `G₂`. -/
theorem measure_stopAtExit_le_of_transfer {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (μ : Measure Ω₁) (ν : Measure Ω₂) (W : Ω₁ → ContinuousPath ℂ)
    (B : Ω₂ → ContinuousPath ℂ) {s : ℝ} (hs : 0 < s) {U : Set ℂ} {T η : ℝ≥0}
    {d d' ε κ δ e a a' : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ}
    (hεκ : 2 * ε < κ) (hκ : 0 < κ)
    (hr : a' + δ + a ≤ min ε d') (A₀ : Set (ℝ≥0 → ℂ))
    (hTrans :
      μ ((fun ω => blockStopped s (farSet U d') N (W ω)) ⁻¹' stopPreimage U A₀) ≤
        ν {ω | ∃ f ∈ stopPreimage U A₀,
            cmpEDist (blockStopped s (farSet U d') N (B ω)) f < ENNReal.ofReal (a' + δ + a)} +
          ENNReal.ofReal e +
          μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}ᶜ +
          ν {ω | (∃ n ≤ N, B ω (blockExitTimes s (farSet U d') n (B ω)) ∈ farSet U d') ∧
            GoodStop U T η d ε (B ω)}ᶜ) :
    μ {ω | stopAtExit U (W ω) ∈ A₀} ≤
      ν {ω | ∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < ENNReal.ofReal κ} +
        ENNReal.ofReal e +
        2 * μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}ᶜ +
        2 * ν {ω | (∃ n ≤ N, B ω (blockExitTimes s (farSet U d') n (B ω)) ∈ farSet U d') ∧
          GoodStop U T η d ε (B ω)}ᶜ := by
  set G₁ : Set Ω₁ := {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}
    with hG₁
  set G₂ : Set Ω₂ := {ω | (∃ n ≤ N, B ω (blockExitTimes s (farSet U d') n (B ω)) ∈ farSet U d') ∧
    GoodStop U T η d ε (B ω)} with hG₂
  set V : Set Ω₂ := {ω | ∃ f ∈ stopPreimage U A₀,
    cmpEDist (blockStopped s (farSet U d') N (B ω)) f < ENNReal.ofReal (a' + δ + a)} with hV
  set V' : Set Ω₂ := {ω | ∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < ENNReal.ofReal κ}
    with hV'
  have h1 : {ω | stopAtExit U (W ω) ∈ A₀} ⊆
      ((fun ω => blockStopped s (farSet U d') N (W ω)) ⁻¹' stopPreimage U A₀) ∪ G₁ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₁
    · exact Or.inl ((blockStopped_mem_stopPreimage_iff hd' hg A₀).2 hω)
    · exact Or.inr hg
  have h2 : V ⊆ V' ∪ G₂ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₂
    · obtain ⟨f, hfA, hf⟩ := hω
      exact Or.inl (exists_mem_of_cmpEDist_blockStopped_lt hs hη hd' hdd hg.2 hg.1 hfA hr hκ hεκ hf)
    · exact Or.inr hg
  calc μ {ω | stopAtExit U (W ω) ∈ A₀}
      ≤ μ (((fun ω => blockStopped s (farSet U d') N (W ω)) ⁻¹' stopPreimage U A₀) ∪ G₁ᶜ) :=
        measure_mono h1
    _ ≤ μ ((fun ω => blockStopped s (farSet U d') N (W ω)) ⁻¹' stopPreimage U A₀) + μ G₁ᶜ :=
        measure_union_le _ _
    _ ≤ (ν V + ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ) + μ G₁ᶜ := by gcongr
    _ ≤ ((ν V' + ν G₂ᶜ) + ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ) + μ G₁ᶜ := by
        gcongr
        exact (measure_mono h2).trans (measure_union_le _ _)
    _ = ν V' + ENNReal.ofReal e + 2 * μ G₁ᶜ + 2 * ν G₂ᶜ := by ring

end BlockExit

end MatedCRT
