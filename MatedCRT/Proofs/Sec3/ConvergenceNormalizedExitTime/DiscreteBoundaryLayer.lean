import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleGreenBound
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenSumBump
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundaryProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Lemma 3.7: the discrete boundary layer

Since every vertex degree is at least one, the normalized expected exit time
`q^ε_A = ∑_b g^ε_A(·, b) / deg^ε(b)` is dominated by the zero-boundary Green
solution `∑_b g^ε_A(·, b)` of `Δ^ε f = -1`. By Lemma 3.5 the rescaled solution
converges uniformly on `cl(B_r(z))` in probability to the continuous solution of
`Δ f̄ = -c₀ μ_h`, `f̄ = 0` on `∂B_r(z)`, which is `6 q̄_{B_r(z)}` by uniqueness of the
Dirichlet problem. The continuum potential is small in a thin deterministic
boundary layer, hence so is the discrete one.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- The normalized exit time is dominated by the zero-boundary Green solution
with a source at most `-1`, because all vertex degrees are at least one. -/
theorem normExitTime_le_finitePoissonSolution {m : ℤ → ℤ → ℕ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (ψ : ℤ → ℝ) (hψ : ∀ b, ψ b ≤ -1) (a : ℤ) :
    normExitTime m A a ≤ finitePoissonSolution m A ψ a := by
  classical
  rw [normExitTime_eq_finset_sum m A hA a]
  simp only [finitePoissonSolution, dite_eq_left hA]
  apply Finset.sum_le_sum
  intro b _
  have hdeg : (1 : ℝ) ≤ (mdeg m b : ℝ) := by
    exact_mod_cast mdeg_pos_of_ne_zero hlf (hcons b)
  have hpos : (0 : ℝ) < (mdeg m b : ℝ) := lt_of_lt_of_le one_pos hdeg
  have hk := Sec7.greenKernel_nonneg m A a b
  unfold greenKernel at hk ⊢
  have hg : 0 ≤ greenFn m A a b := by
    have h := mul_nonneg hk hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at h
  calc greenFn m A a b / (mdeg m b : ℝ) ≤ greenFn m A a b := div_le_self hg hdeg
    _ ≤ -ψ b * greenFn m A a b := le_mul_of_one_le_left hg (by linarith [hψ b])

/-- **Discrete boundary layer of Lemma 3.7.** For every error `δ` and failure
probability `e`, a thin deterministic boundary layer of `B_r(z)` carries rescaled
normalized exit times at most `δ` with probability at least `1 - e`, for all
sufficiently small `ε`. -/
theorem discreteExitBoundary_of_statements
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
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
  obtain ⟨fbar, hpde, hconv, -⟩ := nearPole_controlled_by_dirichlet_limit 𝒮 h35
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

/-- The discrete boundary step of Lemma 3.7 holds, given Lemmas 3.3, 3.5 and 2.17. -/
theorem discreteExitBoundaryStep_of_statements (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮) :
    DiscreteExitBoundaryStep 𝒮 := by
  intro _ _ h217 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball δ hδ e he
  exact discreteExitBoundary_of_statements 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1 S hS hr hball hδ he

/-- **Lemma 3.7** reduced to interior convergence alone: the continuum potential
and the boundary layer are proved from the cited statements. -/
theorem convergenceNormalizedExitTime_of_interior
    (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hinterior : NormalizedExitInteriorStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_interior_discrete_boundary 𝒮 h33 h29 h219 h35 h31 h28 h217
    hinterior (discreteExitBoundaryStep_of_statements 𝒮 h33 h35)

end MatedCRT
