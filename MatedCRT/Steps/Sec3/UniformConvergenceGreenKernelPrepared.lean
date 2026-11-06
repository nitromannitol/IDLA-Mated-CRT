import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Draft.Section3Prepared

/-! Prepared-sequence obligations for Lemma 3.3, corrected paper proof lines 1242–1358.
The interior and boundary steps remain open and must handle almost-sure eventual bounds. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- On a smaller closed ball, compactness and integral convergence identify the Green-kernel
limit uniformly away from the pole (paper, lines 1181–1212). -/
def GreenKernelInteriorPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DegreeMeasureConvergenceStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  GreenKernelUpperBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → DiscretePotentialTightnessPreparedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ r' : ℝ, 0 < r' → r' < r → ∀ O : Set ℂ, O ⊆ closedBall z r' →
  ∀ d : ℝ, 0 < d → (∀ x ∈ O, d ≤ dist y x) →
    TendstoUniformlyOnInProbability S.P (rescaledBallGreenKernel S r z y)
      (fun _ x => S.c₀ / 6 * greenFunction (ball z r) y x) O

/-- The maximum-principle barrier controls the discrepancy in a sufficiently thin boundary
layer away from the pole (paper, lines 1213–1229). -/
def GreenKernelBoundaryPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DegreeMeasureConvergenceStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  GreenKernelUpperBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → DiscretePotentialTightnessPreparedStmt 𝒮 →
  GreenKernelInteriorPreparedStep 𝒮 → MaximumPrincipleStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ δ : ℝ, 0 < δ → ∀ O : Set ℂ, O ⊆ closedBall z r \ {y} → 0 < infDist y O →
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ProbTendsToOne S.P fun ε => {ω | ∀ x ∈ O \ closedBall z r',
        |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ}

/-- Lemma 3.3 from interior identification and boundary control. -/
theorem uniformConvergenceGreenKernel_of_prepared_steps (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hinterior : GreenKernelInteriorPreparedStep 𝒮) (hboundary : GreenKernelBoundaryPreparedStep 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy δ hδ O hO hdist
  obtain ⟨r', hr'0, hr'r, hb⟩ := hboundary h210 h34 h214 h28 h31 hinterior h213 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z y hr hball hy δ hδ O hO hdist
  have hi := hinterior h210 h34 h214 h28 h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z y hr hball hy r' hr'0 hr'r (O ∩ closedBall z r') inter_subset_right
    (infDist y O) hdist (fun x hx => infDist_le_dist_of_mem hx.1) δ hδ
  have hb' : Tendsto (fun ε => S.P {ω | ∃ x ∈ O \ closedBall z r',
      δ < |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x|})
      (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun ε => S.P {ω | ¬ ∀ x, x ∈ O \ closedBall z r' →
      |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ})
      (𝓝[>] 0) (𝓝 0) at hb
    simpa only [not_forall, not_le, not_imp, exists_prop] using hb
  have hs := hi.add hb'
  rw [add_zero] at hs
  unfold ProbTendsToOne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le) fun ε => ?_
  calc
    S.P {ω | ∀ x ∈ O, |rescaledBallGreenKernel S r z y ε ω x -
        S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ}ᶜ ≤
      S.P ({ω | ∃ x ∈ O ∩ closedBall z r', δ < |rescaledBallGreenKernel S r z y ε ω x -
          S.c₀ / 6 * greenFunction (ball z r) y x|} ∪
        {ω | ∃ x ∈ O \ closedBall z r', δ < |rescaledBallGreenKernel S r z y ε ω x -
          S.c₀ / 6 * greenFunction (ball z r) y x|}) := by
      apply measure_mono
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨x, hx, hbad⟩ := hω
      by_cases hx' : x ∈ closedBall z r'
      · exact Or.inl ⟨x, ⟨hx, hx'⟩, hbad⟩
      · exact Or.inr ⟨x, ⟨hx, hx'⟩, hbad⟩
    _ ≤ _ := measure_union_le _ _

end MatedCRT
