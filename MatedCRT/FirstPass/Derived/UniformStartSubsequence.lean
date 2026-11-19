import MatedCRT.FirstPass.Derived.UniformStartGoodFinExit
import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodGSandwich

/-!
# The uniform-start bound from block-exit hypotheses along a subsequence

The uniform-start chain `BlockExitSkeletonGoodGSandwich` → `UniformStartGoodAssembly` assumes the walk-side
block-exit hypotheses almost surely eventually along **every** null sequence of meshes.  Convergence in
probability of the block-exit kernels, which is what the planar invariance principle delivers, gives these
only along a subsequence of a given null sequence (first Borel–Cantelli).  This file reruns the chain with
the walk-side hypotheses (and the reverse Fatou statement) in the subsequence form: for every null sequence
`e` there is a strictly increasing `φ` such that the statement holds almost surely, eventually in `n`, along
`e (φ n)`.

* `ae_eventually_mem_goodG_of_blockExit_sandwich_sub`: the subsequence version of
  `ae_eventually_mem_goodG_of_blockExit_sandwich`.
* `exists_eps_uniformStart_bound_sub`: the subsequence version of `exists_eps_uniformStart_bound_of_gamma`;
  the reverse Fatou statement `hL4sub` (all small `ε`, from a.s. eventually along a subsequence of every null
  sequence) is the general statement for finite measures and is a hypothesis here.
* `gms21UniformStartInput_of_blockExit_sandwich_sub`: the uniform-start statement from the walk-side
  block-exit hypotheses along subsequences.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Metric Set MarkovProcess HarmonicBalls Filter Topology ReflectedGMS.GMS
open scoped NNReal ENNReal
open HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit StopAtExitLevyProkhorov

/-- **Subsequence form of the almost-sure eventual uniform-start event from the block-exit skeleton
comparison.** If for all block parameters with `d' + 2 s ≤ d₁` the walk-side block-exit hypotheses for the
frozen set `ballFrozenSet s (R + d')` hold, almost surely and eventually in `n`, along some subsequence
`e (φ n)`, then almost surely `ω ∈ goodG S (e (φ n)) R ρ κ` for all large `n`, along some subsequence. -/
theorem ae_eventually_mem_goodG_of_blockExit_sandwich_sub {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) (e : ℕ → ℝ) (g : ℝ → ℝ → ℕ)
    (hwalk : ∀ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → d' + 2 * s ≤ d₁ → 0 < δ₀ → g s d' ≤ N →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (ballFrozenSet s (R + d')) j b) ∈
          ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal (κ / 16)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e (φ n)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e (φ n)) ω) x).map fun ξ =>
              blockExitPositions s (ballFrozenSet s (R + d')) N
                (interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e (φ n)) (S.η ω) x)).map fun b =>
              blockExitPositions s (ballFrozenSet s (R + d')) N b) δ₀ (κ / 4) ∧
          srwLaw (S.mult (e (φ n)) ω) x {ξ | ∃ j ≤ N,
              interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (ballFrozenSet s (R + d')) j
                (interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ)) ∈
              ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal (κ / 8)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e (φ n)) R ρ κ := by
  obtain ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, hgN, H⟩ :=
    exists_blockExit_parameters_mem_goodG_sandwich hρ hρR hκ g
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  obtain ⟨hguard, H'⟩ := H (measurableSet_ballFrozenSet s (R + d'))
    (farSet_subset_ballFrozenSet hs hR hd' hd₁) (ballFrozenSet_subset_farSet s R d')
  obtain ⟨φ, hφ, hω⟩ := hwalk s d' d₁ δ₀ N hs hd' hd₁ hδ₀ hgN hguard
  exact ⟨φ, hφ, hω.mono fun ω hω => hω.mono fun n hn => H' S (e (φ n)) ω hn⟩

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Fixed-`ε` uniform-start bound from the almost-sure eventual statement along subsequences.** As
`exists_eps_uniformStart_bound_of_gamma`, with the covering statement `hpkg` and the reverse Fatou statement
`hL4sub` required only along a subsequence of each null sequence. -/
theorem exists_eps_uniformStart_bound_sub {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ}
    (hL4sub : ∀ M : ℝ → Set Ω, (∀ ε : ℝ, 0 < ε → MeasurableSet (M ε)) →
      (∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ M (e (φ n))) →
      ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P (M ε)ᶜ ≤ ENNReal.ofReal θ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpkg : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e (φ n)) R ρ (κ / 2))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.P (goodG S ε R ρ κ)ᶜ ≤ ENNReal.ofReal θ := by
  obtain ⟨η', hη'm, hη'ae⟩ := hS.exists_curveVersion
  have : Nonempty (BouRabeeGwynne.CurveSpace 2) :=
    ⟨stoppedExitCurve (ball (0 : ℂ) R) 0⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (BouRabeeGwynne.CurveSpace 2)
  have hMm : ∀ ε : ℝ, 0 < ε → MeasurableSet (goodM S η' d ε R ρ (κ / 2)) := fun ε _ =>
    measurableSet_goodM hS hη'm d ε R ρ (κ / 2)
  have hseq : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodM S η' d (e (φ n)) R ρ (κ / 2) := by
    intro e he he0
    obtain ⟨φ, hφ, hpe⟩ := hpkg e he he0
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hpe, ae_all_iff.2 fun n => ae_mem_finExit hγ hγ2 hS (he (φ n)) R ρ, hη'ae]
      with ω h1 h2 h3
    exact h1.mono fun n hn => mem_goodM_of_mem_goodG d (by positivity) h3 (h2 n) hn
  obtain ⟨ε₀, hε₀, hε⟩ := hL4sub _ hMm hseq θ hθ
  refine ⟨ε₀, hε₀, fun ε hε0 hεε₀ => ?_⟩
  have hnull : S.P {ω | ¬ ⇑(η' ω) = S.η ω} = 0 := by
    rw [ae_iff] at hη'ae; exact hη'ae
  calc S.P (goodG S ε R ρ κ)ᶜ
      ≤ S.P ((goodM S η' d ε R ρ (κ / 2))ᶜ ∪ {ω | ¬ ⇑(η' ω) = S.η ω}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hcon
        exact hω (mem_goodG_of_mem_goodM hd hκ hcon.2 hcon.1)
    _ ≤ S.P (goodM S η' d ε R ρ (κ / 2))ᶜ + S.P {ω | ¬ ⇑(η' ω) = S.η ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal θ := by rw [hnull, add_zero]; exact hε ε hε0 hεε₀

/-- **The uniform-start invariance principle from the walk-side block-exit hypotheses along subsequences,
frozen on a union of grid cells.** As `gms21UniformStartInput_of_blockExit_sandwich`, with the walk-side
hypotheses required along some subsequence of each null sequence of meshes, and with the reverse Fatou
statement along subsequences (`hL4sub`) for finite measures. -/
theorem gms21UniformStartInput_of_blockExit_sandwich_sub {𝒮 : SpaceFillingSLEModel}
    (hL4sub : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (M : ℝ → Set Ω),
      (∀ ε : ℝ, 0 < ε → MeasurableSet (M ε)) →
      (∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ M (e (φ n))) →
      ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → P (M ε)ᶜ ≤ ENNReal.ofReal θ)
    (g : ℝ → ℝ → ℝ → ℝ → ℕ)
    (hwalk : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ →
      ∀ (e : ℕ → ℝ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → d' + 2 * s ≤ d₁ → 0 < δ₀ →
      g R κ s d' ≤ N →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (ballFrozenSet s (R + d')) j b) ∈
          ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 16)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e (φ n)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e (φ n)) ω) x).map fun ξ =>
              blockExitPositions s (ballFrozenSet s (R + d')) N
                (interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e (φ n)) (S.η ω) x)).map fun b =>
              blockExitPositions s (ballFrozenSet s (R + d')) N b) δ₀ ((κ / 2) / 4) ∧
          srwLaw (S.mult (e (φ n)) ω) x {ξ | ∃ j ≤ N,
              interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (ballFrozenSet s (R + d')) j
                (interpPathCM (vertexPoint (e (φ n)) (S.η ω)) zero_le_one ξ)) ∈
              ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 8)) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact exists_eps_uniformStart_bound_sub hγ hγ2 hS (fun M hM h θ' hθ' => hL4sub S.P M hM h θ' hθ') hκ
    (fun e he he0 => ae_eventually_mem_goodG_of_blockExit_sandwich_sub S hρ.le hρR (half_pos hκ) e (g R κ)
      (hwalk γ hγ hγ2 Ω S hS R ρ hρ hρR κ hκ e he he0)) hθ

end UniformStartGood

end MatedCRT
