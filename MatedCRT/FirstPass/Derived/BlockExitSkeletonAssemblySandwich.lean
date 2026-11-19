import MatedCRT.FirstPass.Derived.BlockExitSkeletonAssembly
import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodStopSandwich

/-!
# Block-exit skeleton comparison of stopped paths: chain frozen on a sandwiched set

The pointwise inclusions of `BlockExitSkeletonEvents` and the measure assembly of
`BlockExitSkeletonAssembly`, for a block-exit chain frozen on a closed set `F` that is only
sandwiched between far sets of the open set `U`: `farSet U d₁ ⊆ F ⊆ farSet U d'` (with
`0 < d'`, `4 s + d₁ ≤ d`), instead of `F = farSet U d'`. A staircase grid polygon
`P` with `U.thickening d' ⊆ P ⊆ U.thickening d₁` and `F = Pᶜ` is an instance.

* `stopAtExit_blockStopped_eq_of_subset`, `blockStopped_mem_stopPreimage_iff_of_subset`: walk side;
* `exists_mem_of_cmpEDist_blockStopped_lt_sandwich`: Brownian side on the good event;
* `measure_stopAtExit_le_of_transfer_sandwich`: the measure assembly, conditional on the transfer
  bound `hTrans`.
-/

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- If the chain frozen on `F` reaches `F` within `N` steps, the path is in `F` at the `N`-th block
exit. -/
theorem blockExit_mem_of_exists {s : ℝ} {F : Set ℂ} {N : ℕ} {ω : ContinuousPath ℂ}
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) : ω (blockExitTimes s F N ω) ∈ F := by
  classical
  obtain ⟨hMN, hM⟩ : Nat.find hF ≤ N ∧ ω (blockExitTimes s F (Nat.find hF) ω) ∈ F :=
    Nat.find_spec hF
  rw [blockExitTimes_eq_of_mem s hM N hMN]
  exact hM

/-- **Walk side.** For `F ⊆ farSet U d'`, the path stopped at the `N`-th block exit has the same
stopped path at the exit time from `U` as the path itself, once the chain has reached `F`. -/
theorem stopAtExit_blockStopped_eq_of_subset {s : ℝ} {U F : Set ℂ} {d' : ℝ} (hd' : 0 < d')
    (hF₂ : F ⊆ farSet U d') {N : ℕ} {ω : ContinuousPath ℂ}
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) :
    stopAtExit U (blockStopped s F N ω) = stopAtExit U ω :=
  stopAtExit_comp_min_eq ((mem_farSet.1 (hF₂ (blockExit_mem_of_exists hF))) _
    (by rw [dist_self]; exact hd'))

theorem blockStopped_mem_stopPreimage_iff_of_subset {s : ℝ} {U F : Set ℂ} {d' : ℝ} (hd' : 0 < d')
    (hF₂ : F ⊆ farSet U d') {N : ℕ} {ω : ContinuousPath ℂ}
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) (A : Set (ℝ≥0 → ℂ)) :
    blockStopped s F N ω ∈ stopPreimage U A ↔ stopAtExit U ω ∈ A := by
  show stopAtExit U (blockStopped s F N ω) ∈ A ↔ _
  rw [stopAtExit_blockStopped_eq_of_subset hd' hF₂ hF]

/-- **Brownian side**, for a sandwiched frozen set `farSet U d₁ ⊆ F ⊆ farSet U d'`. -/
theorem exists_mem_of_cmpEDist_blockStopped_lt_sandwich {s : ℝ} (hs : 0 < s) {U F : Set ℂ}
    {T η : ℝ≥0} {d d₁ d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d') (hd'd : d' ≤ d) (hdd : 4 * s + d₁ ≤ d)
    (hF₁ : farSet U d₁ ⊆ F) (hF₂ : F ⊆ farSet U d') {N : ℕ} {ω : ContinuousPath ℂ}
    (hgood : GoodStop U T η d ε ω) (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F)
    {A : Set (ℝ≥0 → ℂ)} {f : ℝ≥0 → ℂ} (hfA : f ∈ stopPreimage U A) {r κ : ℝ}
    (hr : r ≤ min ε d') (hκ : 0 < κ) (hεκ : 2 * ε < κ)
    (hf : cmpEDist (blockStopped s F N ω) f < ENNReal.ofReal r) :
    ∃ f' ∈ A, cmpEDist (stopAtExit U ω) f' < ENNReal.ofReal κ := by
  refine ⟨stopAtExit U f, hfA, ?_⟩
  have hf' : cmpEDist f (blockStopped s F N ω) < ENNReal.ofReal (min ε d') := by
    rw [cmpEDist_comm]
    exact lt_of_lt_of_le hf (ENNReal.ofReal_le_ofReal hr)
  have h := cmpEDist_stopAtExit_le_of_goodStop_blockExit_sandwich hs hη hd' hd'd hdd hF₁ hF₂
    hgood hF hf'
  rw [cmpEDist_comm]
  exact lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff hκ).2 hεκ)

/-- **Measure assembly (conditional on the transfer bound), sandwiched frozen set.** The statement
of `measure_stopAtExit_le_of_transfer` for a chain frozen on `F` with
`farSet U d₁ ⊆ F ⊆ farSet U d'`. -/
theorem measure_stopAtExit_le_of_transfer_sandwich {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (μ : Measure Ω₁) (ν : Measure Ω₂) (W : Ω₁ → ContinuousPath ℂ)
    (B : Ω₂ → ContinuousPath ℂ) {s : ℝ} (hs : 0 < s) {U F : Set ℂ} {T η : ℝ≥0}
    {d d₁ d' ε κ δ e a a' : ℝ} (hη : 0 < η) (hd' : 0 < d') (hd'd : d' ≤ d)
    (hdd : 4 * s + d₁ ≤ d) (hF₁ : farSet U d₁ ⊆ F) (hF₂ : F ⊆ farSet U d') {N : ℕ}
    (hεκ : 2 * ε < κ) (hκ : 0 < κ)
    (hr : a' + δ + a ≤ min ε d') (A₀ : Set (ℝ≥0 → ℂ))
    (hTrans :
      μ ((fun ω => blockStopped s F N (W ω)) ⁻¹' stopPreimage U A₀) ≤
        ν {ω | ∃ f ∈ stopPreimage U A₀,
            cmpEDist (blockStopped s F N (B ω)) f < ENNReal.ofReal (a' + δ + a)} +
          ENNReal.ofReal e +
          μ {ω | ∃ n ≤ N, W ω (blockExitTimes s F n (W ω)) ∈ F}ᶜ +
          ν {ω | (∃ n ≤ N, B ω (blockExitTimes s F n (B ω)) ∈ F) ∧
            GoodStop U T η d ε (B ω)}ᶜ) :
    μ {ω | stopAtExit U (W ω) ∈ A₀} ≤
      ν {ω | ∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < ENNReal.ofReal κ} +
        ENNReal.ofReal e +
        2 * μ {ω | ∃ n ≤ N, W ω (blockExitTimes s F n (W ω)) ∈ F}ᶜ +
        2 * ν {ω | (∃ n ≤ N, B ω (blockExitTimes s F n (B ω)) ∈ F) ∧
          GoodStop U T η d ε (B ω)}ᶜ := by
  set G₁ : Set Ω₁ := {ω | ∃ n ≤ N, W ω (blockExitTimes s F n (W ω)) ∈ F} with hG₁
  set G₂ : Set Ω₂ := {ω | (∃ n ≤ N, B ω (blockExitTimes s F n (B ω)) ∈ F) ∧
    GoodStop U T η d ε (B ω)} with hG₂
  set V : Set Ω₂ := {ω | ∃ f ∈ stopPreimage U A₀,
    cmpEDist (blockStopped s F N (B ω)) f < ENNReal.ofReal (a' + δ + a)} with hV
  set V' : Set Ω₂ := {ω | ∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < ENNReal.ofReal κ}
    with hV'
  have h1 : {ω | stopAtExit U (W ω) ∈ A₀} ⊆
      ((fun ω => blockStopped s F N (W ω)) ⁻¹' stopPreimage U A₀) ∪ G₁ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₁
    · exact Or.inl ((blockStopped_mem_stopPreimage_iff_of_subset hd' hF₂ hg A₀).2 hω)
    · exact Or.inr hg
  have h2 : V ⊆ V' ∪ G₂ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₂
    · obtain ⟨f, hfA, hf⟩ := hω
      exact Or.inl (exists_mem_of_cmpEDist_blockStopped_lt_sandwich hs hη hd' hd'd hdd hF₁ hF₂
        hg.2 hg.1 hfA hr hκ hεκ hf)
    · exact Or.inr hg
  calc μ {ω | stopAtExit U (W ω) ∈ A₀}
      ≤ μ (((fun ω => blockStopped s F N (W ω)) ⁻¹' stopPreimage U A₀) ∪ G₁ᶜ) :=
        measure_mono h1
    _ ≤ μ ((fun ω => blockStopped s F N (W ω)) ⁻¹' stopPreimage U A₀) + μ G₁ᶜ :=
        measure_union_le _ _
    _ ≤ (ν V + ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ) + μ G₁ᶜ := by gcongr
    _ ≤ ((ν V' + ν G₂ᶜ) + ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ) + μ G₁ᶜ := by
        gcongr
        exact (measure_mono h2).trans (measure_union_le _ _)
    _ = ν V' + ENNReal.ofReal e + 2 * μ G₁ᶜ + 2 * ν G₂ᶜ := by ring

end BlockExit

end MatedCRT
