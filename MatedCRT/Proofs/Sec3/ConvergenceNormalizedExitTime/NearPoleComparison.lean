import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpDirichlet
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb

/-! # Near-pole comparison in the mated-CRT environment -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- On the small-cell event, the missing part of the rescaled Green sum is
bounded by the rescaled Green solution with negative buffered-bump source. -/
theorem MatedCRTEnv.IsValid.ae_nearPole_le_poissonSolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (z y : ℂ) (r δ : ℝ) (hball : ball z r ⊆ ball 0 ρ)
    (φ : ℂ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hone : ∀ x ∈ ball y (δ + δ), φ x = 1) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε →
      (∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), diam (cell ε (S.η ω) b) ≤ δ) →
      0 ≤ rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
        (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b ∧
      rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
        (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b ≤
      rescale (S.mε ε) ε (S.η ω)
        (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => -φ (vertexPoint ε (S.η ω) b))) y := by
  filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 hcell,
    hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hlf hp harea
  intro ε hε hdiam
  let A := interiorCellVertices ε (S.η ω) (ball z r)
  have hA : A.Finite := (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset
    (by intro b hb; exact hb.1)
  have hM : 0 ≤ S.mε ε := medianOf_nonneg _
  apply rescaledExitTime_sub_truncated_le_bump harea.1 hp hε hM z y r δ δ
    (S.mult ε ω) (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) φ _ ?_ hone ?_ ?_ ?_
  · intro b hb
    apply hdiam b
    exact Sec7.cellVertices_mono hball hb.1.1
  · intro b hb
    exact hφ0 _
  · intro b hb
    exact finitePoissonSolution_zero hA _ hb
  · intro b hb
    exact finitePoissonSolution_laplacian (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) hA _ hb

/-- A comparison valid on events of probability tending to one passes to a
tail bound for the limit of the dominating random variables. -/
theorem eventually_measure_gt_le_of_compare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω)
    (F G : ℝ → Ω → ℝ) (U : Ω → ℝ)
    (hcompare : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ω ∈ E ε → F ε ω ≤ G ε ω)
    (hsmall : ProbTendsToOne P E) (hconv : TendstoInProbability P G U)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P {ω | 2 * t < F ε ω} ≤ P {ω | t < U ω} + e := by
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have hE := ENNReal.tendsto_nhds_zero.1 hsmall (e / 2) he2
  have hG := ENNReal.tendsto_nhds_zero.1 (hconv t ht) (e / 2) he2
  filter_upwards [hE, hG, self_mem_nhdsWithin] with ε hEε hGε hε
  calc
    P {ω | 2 * t < F ε ω} ≤
        P ({ω | t < U ω} ∪ ((E ε)ᶜ ∪ {ω | t < |G ε ω - U ω|})) := by
      apply measure_mono_ae
      filter_upwards [hcompare ε hε] with ω hw
      intro hF
      by_contra hn
      have hU : U ω ≤ t := le_of_not_gt (fun h => hn (Or.inl h))
      have hE : ω ∈ E ε := by
        by_contra h
        exact hn (Or.inr (Or.inl h))
      have hG : |G ε ω - U ω| ≤ t :=
        le_of_not_gt (fun h => hn (Or.inr (Or.inr h)))
      have hgu := (abs_le.mp hG).2
      linarith [hw hE]
    _ ≤ P {ω | t < U ω} + (P (E ε)ᶜ + P {ω | t < |G ε ω - U ω|}) := by
      exact (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ P {ω | t < U ω} + e := by
      gcongr
      calc
        _ ≤ e / 2 + e / 2 := add_le_add hEε hGε
        _ = e := ENNReal.add_halves e

/-- The near-pole error is controlled in probability by the continuum
Dirichlet limit for the buffered bump. -/
theorem nearPole_controlled_by_dirichlet_limit
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (φ : ℂ → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ ball y (δ + δ), φ x = 1)
    (hholder : IsHolderContinuousOn φ (ball z r)) :
    ∃ fbar : Ω → ℂ → ℝ,
      (∀ᵐ ω ∂S.P, ContinuousOn (fbar ω) (closedBall z r) ∧
        HasLaplacian (fbar ω)
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * -φ x))
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * -φ x))) (ball z r) ∧
        (∀ x ∈ sphere z r, fbar ω x = 0) ∧ IsHolderContinuousOn (fbar ω) (closedBall z r)) ∧
      TendstoUniformlyOnInProbability S.P
        (fun ε ω => rescale (S.mε ε) ε (S.η ω)
          (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (fun b => -φ (vertexPoint ε (S.η ω) b)))) fbar (closedBall z r) ∧
      ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          S.P {ω | 2 * t < rescale (S.mε ε) ε (S.η ω)
                (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
              (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
                greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
                  (vertexOf ε (S.η ω) y) b} ≤ S.P {ω | t < fbar ω y} + e := by
  have hneg : IsHolderContinuousOn (fun x => -φ x) (ball z r) := by
    obtain ⟨C, α, hα, hα1, h⟩ := hholder
    refine ⟨C, α, hα, hα1, ?_⟩
    intro x hx x' hx'
    simpa only [edist_neg_neg] using h x hx x' hx'
  have hbound : ∃ M : ℝ, ∀ x ∈ ball z r, |-φ x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x hx
    rw [abs_neg, abs_of_nonneg (hφ x).1]
    exact (hφ x).2
  obtain ⟨fbar, hpde, hconv⟩ := finitePoissonSolution_converges 𝒮 h35 hcell
    hγ hγ2 hρ hρ1 S hS hr hball (fun x => -φ x) hbound hneg
  refine ⟨fbar, hpde, hconv, ?_⟩
  let G : ℝ → Ω → ℝ := fun ε ω => rescale (S.mε ε) ε (S.η ω)
    (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
      (fun b => -φ (vertexPoint ε (S.η ω) b))) y
  have hpoint : TendstoInProbability S.P G (fun ω => fbar ω y) := by
    intro t ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv t ht)
      (fun _ => zero_le)
    intro ε
    apply measure_mono
    intro ω hω
    exact ⟨y, ball_subset_closedBall hy, hω⟩
  intro t ht e he
  apply eventually_measure_gt_le_of_compare S.P
    (fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      diam (cell ε (S.η ω) b) ≤ δ}) _ G (fun ω => fbar ω y) ?_
    (hS.probTendsToOne_small_cells ρ δ hδ) hpoint ht he
  intro ε hε
  filter_upwards [hS.ae_nearPole_le_poissonSolution hγ hγ2 hcell z y r δ hball φ
    (fun x => (hφ x).1) hone] with ω hω hdiam
  exact (hω ε hε hdiam).2

end MatedCRT
