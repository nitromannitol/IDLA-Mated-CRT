import MatedCRT.FirstPass.Derived.UniformStartGoodSandwich

/-!
# Assembly of the uniform-start bound from an almost-sure eventual statement

Along every positive sequence `e n → 0`, suppose that almost surely the uniform-start event at tolerance
`κ / 2` holds eventually (this is the form in which the covering-package statement is delivered), that the
interpolated walk exits `ball 0 R` almost surely for every cell size, and that measurable events holding
almost surely eventually along every sequence satisfy the small-`ε` bound (reverse Fatou, the hypothesis
`hL4`).  Then for every `θ > 0` there is `ε₀ > 0` such that for all `ε ∈ (0, ε₀)` the uniform-start event at
tolerance `κ` has probability at least `1 - θ`: this is the shape of the uniform-start invariance
principle (`goodG` is the event inside the probability bound).  The measurable sandwich `goodM` of
`UniformStartGoodSandwich` turns the almost-sure-along-sequences statement into a statement at fixed `ε`.
-/

open MeasureTheory ProbabilityTheory Metric Set MarkovProcess HarmonicBalls Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT.UniformStartGood

open StopAtExitLevyProkhorov

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Fixed-`ε` uniform-start bound from the almost-sure eventual statement.** `hL4` is the reverse Fatou
lemma for the probability measure `S.P` (events measurable for `ε > 0` that hold almost surely eventually
along every positive sequence tending to `0` have small complement for all small `ε`); `hfin` is the almost
sure exit of the interpolated walk from `ball 0 R`; `hpkg` is the almost-sure eventual uniform-start
statement at tolerance `κ / 2`. -/
theorem exists_eps_uniformStart_bound {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {R ρ : ℝ}
    (hL4 : ∀ M : ℝ → Set Ω, (∀ ε : ℝ, 0 < ε → MeasurableSet (M ε)) →
      (∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
        ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ M (e n)) →
      ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P (M ε)ᶜ ≤ ENNReal.ofReal θ)
    (hfin : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ finExit S ε R ρ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpkg : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ (κ / 2))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.P (goodG S ε R ρ κ)ᶜ ≤ ENNReal.ofReal θ := by
  obtain ⟨η', hη'm, hη'ae⟩ := hS.exists_curveVersion
  have : Nonempty (BouRabeeGwynne.CurveSpace 2) :=
    ⟨stoppedExitCurve (ball (0 : ℂ) R) 0⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (BouRabeeGwynne.CurveSpace 2)
  have hMm : ∀ ε : ℝ, 0 < ε → MeasurableSet (goodM S η' d ε R ρ (κ / 2)) := fun ε _ =>
    measurableSet_goodM hS hη'm d ε R ρ (κ / 2)
  have hseq : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodM S η' d (e n) R ρ (κ / 2) := by
    intro e he he0
    filter_upwards [hpkg e he he0, ae_all_iff.2 fun n => hfin (e n) (he n), hη'ae] with ω h1 h2 h3
    exact h1.mono fun n hn => mem_goodM_of_mem_goodG d (by positivity) h3 (h2 n) hn
  obtain ⟨ε₀, hε₀, hε⟩ := hL4 _ hMm hseq θ hθ
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

end MatedCRT.UniformStartGood
