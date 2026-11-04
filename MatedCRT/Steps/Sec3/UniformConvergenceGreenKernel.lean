import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3

/-!
# Lemma 3.3: convergence of the Green kernel

The two steps isolate identification of the interior limit and the maximum-principle
boundary argument, respectively. The limit uses the corrected constant `c₀ / 6`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The rescaled discrete Green kernel in Lemma 3.3. -/
noncomputable def rescaledGreenKernel {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z y : ℂ) (ε : ℝ) (ω : Ω) : ℂ → ℝ :=
  rescale (S.mε ε) ε (S.η ω)
    (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
      (vertexOf ε (S.η ω) y) a)

/-- On a smaller closed ball, compactness and integral convergence identify the Green-kernel
limit uniformly away from the pole (paper, lines 1181–1212). -/
def GreenKernelInteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DegreeMeasureConvergenceStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  GreenKernelUpperBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → DiscretePotentialTightnessStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ r' : ℝ, 0 < r' → r' < r → ∀ O : Set ℂ, O ⊆ closedBall z r' →
  ∀ d : ℝ, 0 < d → (∀ x ∈ O, d ≤ dist y x) →
    TendstoUniformlyOnInProbability S.P (rescaledGreenKernel S r z y)
      (fun _ x => S.c₀ / 6 * greenFunction (ball z r) y x) O

/-- The maximum-principle barrier controls the discrepancy in a sufficiently thin boundary
layer away from the pole (paper, lines 1213–1229). -/
def GreenKernelBoundaryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DegreeMeasureConvergenceStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  GreenKernelUpperBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → DiscretePotentialTightnessStmt 𝒮 →
  GreenKernelInteriorStep 𝒮 → MaximumPrincipleStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ δ : ℝ, 0 < δ → ∀ O : Set ℂ, O ⊆ closedBall z r \ {y} → 0 < infDist y O →
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ProbTendsToOne S.P fun ε => {ω | ∀ x ∈ O \ closedBall z r',
        |rescaledGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ}

/-- Lemma 3.3 from interior identification and boundary control. -/
theorem uniformConvergenceGreenKernel_of_steps (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hinterior : GreenKernelInteriorStep 𝒮) (hboundary : GreenKernelBoundaryStep 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy δ hδ O hO hdist
  obtain ⟨r', hr'0, hr'r, hb⟩ := hboundary h210 h34 h214 h28 h31 hinterior h213 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z y hr hball hy δ hδ O hO hdist
  have hi := hinterior h210 h34 h214 h28 h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z y hr hball hy r' hr'0 hr'r (O ∩ closedBall z r') inter_subset_right
    (infDist y O) hdist (fun x hx => infDist_le_dist_of_mem hx.1) δ hδ
  have hb' : Tendsto (fun ε => S.P {ω | ∃ x ∈ O \ closedBall z r',
      δ < |rescaledGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x|})
      (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun ε => S.P {ω | ¬ ∀ x, x ∈ O \ closedBall z r' →
      |rescaledGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ})
      (𝓝[>] 0) (𝓝 0) at hb
    simpa only [not_forall, not_le, not_imp, exists_prop] using hb
  have hs := hi.add hb'
  rw [add_zero] at hs
  unfold ProbTendsToOne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le) fun ε => ?_
  calc
    S.P {ω | ∀ x ∈ O, |rescaledGreenKernel S r z y ε ω x -
        S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ}ᶜ ≤
      S.P ({ω | ∃ x ∈ O ∩ closedBall z r', δ < |rescaledGreenKernel S r z y ε ω x -
          S.c₀ / 6 * greenFunction (ball z r) y x|} ∪
        {ω | ∃ x ∈ O \ closedBall z r', δ < |rescaledGreenKernel S r z y ε ω x -
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
