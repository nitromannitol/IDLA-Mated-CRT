import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CorrectedNearPoleSmall
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.InteriorDiscreteModulus
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DiscreteBoundaryLayer

/-! Interior and boundary exit-time estimates under projected Dirichlet data. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Pointwise convergence and a probabilistic modulus for the discrete exit
times imply uniform interior convergence in probability. -/
theorem normalizedExitInterior_of_discrete_modulus_corrected
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ)
    (hmod : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r',
        dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x -
          rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y|} ≤ e) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r') := by
  apply uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r') _ _
  · intro x hx
    apply pointwise_normalizedExitTime_of_corrected_inputs 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1 S hS hr hball
    exact (mem_ball).2 ((mem_closedBall.1 hx).trans_lt hr')
  · exact hmod
  · intro t ht e he
    exact normalizedExitGreenPotential_modulus_small 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hr'
      hball ht he


/-- Boundary-layer control under the corrected Dirichlet statement. -/
theorem discreteExitBoundary_of_corrected_statements
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {δ : ℝ} (hδ : 0 < δ) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ≤ e := by
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  let φ : ℂ → ℝ := fun _ => 1
  have hholder : IsHolderContinuousOn φ (ball z r) :=
    ⟨0, 1, zero_lt_one, le_rfl, (LipschitzWith.const (1 : ℝ)).holderWith.holderOnWith _⟩
  have hzmem : z ∈ ball z r := mem_ball_self hr
  obtain ⟨fbar, hpde, hconv, -⟩ := nearPole_controlled_by_dirichlet_limit_corrected 𝒮 h35
    (adjacentCellsMeetAeStep 𝒮) hγ hγ2 hρ hρ1 S hS hr one_pos hball hzmem φ
    (fun _ => ⟨zero_le_one, le_rfl⟩) (fun _ _ => rfl) hholder
  have hq := weightedGreenPotential_ae_satisfies_dirichlet 𝒮 h217
    hγ hγ2 hρ hρ1 S hS hr hball φ measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)
  have hident : ∀ᵐ ω ∂S.P, ∀ x ∈ closedBall z r,
      fbar ω x = 6 * normalizedExitGreenPotential S r z ω x := by
    filter_upwards [hpde, hq] with ω hf hqω
    intro x hx
    have h := eqOn_closedBall_of_hasLaplacian_eq hf.1 hqω.1 hf.2.1 hqω.2.1
      (fun x hx => (hf.2.2.1 x hx).trans (hqω.2.2 x hx).symm) hx
    rw [h]
    simp only [normalizedExitGreenPotential, φ, mul_one]
    ring
  have hcmp : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ x : ℂ,
      0 ≤ rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x ∧
      rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x ≤
      rescale (S.mε ε) ε (S.η ω)
        (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => -φ (vertexPoint ε (S.η ω) b))) x := by
    filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮),
      hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hlf hp harea
    intro ε hε x
    have hA : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
      (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset (fun b hb => hb.1)
    have hM : 0 ≤ (S.mε ε)⁻¹ := inv_nonneg.2 (medianOf_nonneg _)
    unfold rescale
    refine ⟨mul_nonneg hM (normExitTime_nonneg _ _ _), mul_le_mul_of_nonneg_left ?_ hM⟩
    exact normExitTime_le_finitePoissonSolution (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) hA _
      (fun b => le_of_eq (by simp only [φ])) _
  obtain ⟨r', hr'0, hr'r, hpot⟩ := normalizedExitGreenPotential_boundary_small_of_statements
    𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball (show (0 : ℝ) < δ / 12 by positivity) he2
  refine ⟨r', hr'0, hr'r, ?_⟩
  have hsmall := ENNReal.tendsto_nhds_zero.1 (hconv (δ / 2) (by positivity)) (e / 2) he2
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hεpos
  calc
    S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ≤
      S.P ({ω | ∃ x ∈ closedBall z r, δ / 2 < |rescale (S.mε ε) ε (S.η ω)
          (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (fun b => -φ (vertexPoint ε (S.η ω) b))) x - fbar ω x|} ∪
        {ω | ∃ x ∈ closedBall z r \ closedBall z r',
          δ / 12 < |normalizedExitGreenPotential S r z ω x|}) := by
        apply measure_mono_ae
        filter_upwards [hident, hcmp] with ω hid hc
        rintro ⟨x, hx, hbig⟩
        by_contra hn
        have hxK : x ∈ closedBall z r := hx.1
        have a1 : |rescale (S.mε ε) ε (S.η ω)
            (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
              (fun b => -φ (vertexPoint ε (S.η ω) b))) x - fbar ω x| ≤ δ / 2 :=
          le_of_not_gt fun h => hn (Or.inl ⟨x, hxK, h⟩)
        have a2 : |normalizedExitGreenPotential S r z ω x| ≤ δ / 12 :=
          le_of_not_gt fun h => hn (Or.inr ⟨x, hx, h⟩)
        obtain ⟨h0, hle⟩ := hc ε hεpos x
        rw [abs_of_nonneg h0] at hbig
        rw [hid x hxK] at a1
        have b1 := (abs_le.mp a1).2
        have b2 := (abs_le.mp a2).2
        linarith
    _ ≤ e / 2 + e / 2 := (measure_union_le _ _).trans (add_le_add hε hpot)
    _ = e := ENNReal.add_halves e

end MatedCRT

#print axioms MatedCRT.normalizedExitInterior_of_discrete_modulus_corrected
#print axioms MatedCRT.discreteExitBoundary_of_corrected_statements
