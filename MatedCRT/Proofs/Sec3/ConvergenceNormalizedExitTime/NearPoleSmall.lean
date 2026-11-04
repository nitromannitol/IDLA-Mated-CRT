import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleAbsoluteBound
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.UniformBumpProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.SmallBallGeometry
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BufferedBump
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PointwiseConvergence

/-! Smallness in probability of the discrete near-pole Green sum. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- Lemmas 3.5 and 2.17 make the discrete near-pole error uniformly small
as the truncation radius decreases. -/
theorem nearPole_small_in_probability
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ R : ℝ, 0 < R ∧
      ∀ δ : ℝ, 0 < δ → δ < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        S.P {ω | t < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
          (S.mε ε)⁻¹ * ∑ a ∈ truncatedGreenCells ε (S.η ω) z y r δ,
            greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
              (vertexOf ε (S.η ω) y) a|} < e := by
  intro t ht e he
  let b := min e 1
  let d := b / 2 / 2 / 2
  have hb : 0 < b := lt_min he zero_lt_one
  have hbtop : b ≠ ⊤ := ne_of_lt ((min_le_right e 1).trans_lt ENNReal.one_lt_top)
  have hd : 0 < d := ENNReal.half_pos (ENNReal.half_pos (ENNReal.half_pos hb.ne').ne').ne'
  have hsum : (d + d) + d ≤ b / 2 := by
    calc
      (d + d) + d ≤ (d + d) + (d + d) :=
        add_le_add (le_refl (d + d)) (le_add_of_nonneg_right (show 0 ≤ d from zero_le))
      _ = b / 2 := by dsimp [d]; rw [ENNReal.add_halves, ENNReal.add_halves]
  have hlt : b / 2 < e := (ENNReal.half_lt_self hb.ne' hbtop).trans_le (min_le_left e 1)
  have hy0 : y ∈ ball (0 : ℂ) ρ := hball hy
  have hgeom := ball_subset_closedBall_two_of_subset_unit hρ1 hball hy
  have hconv := uniformBumpPotential_tendstoInProbability_zero h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField hy0 hgeom hy S.c₀_nonneg (t / 2) (by linarith)
  have hsmall := ENNReal.tendsto_nhds_zero.1 hconv d hd
  obtain ⟨R, hR, hRbound⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hsmall)
  refine ⟨R / 4, by positivity, ?_⟩
  intro δ hδ hδR
  have h4δ : 0 < 4 * δ := by positivity
  have h4δR : dist (4 * δ) 0 < R := by
    rw [Real.dist_eq, sub_zero, abs_of_pos h4δ]
    linarith
  have hprob := hRbound h4δR h4δ
  obtain ⟨φ, hφ, hone, hsupp, hholder⟩ := exists_buffered_holder_bump y hδ
  obtain ⟨C, α, hα, _, hh⟩ := hholder Set.univ
  have hφm : Measurable φ := (continuousOn_univ.mp (hh.continuousOn hα)).measurable
  have hone' : ∀ x ∈ ball y (δ + δ), φ x = 1 := by simpa [two_mul] using hone
  have htail := nearPole_absolute_controlled_by_greenPotential 𝒮 h35 h217
    hγ hγ2 hρ hρ1 S hS hr hδ hball hy φ hφm hφ hone' (hholder _) (show 0 < t / 2 by linarith) hd
  have hpot : S.P {ω | t / 2 < S.c₀ * ∫ w in ball z r,
      greenFunction (ball z r) y w * φ w ∂S.μ ω} ≤ d := by
    refine (measure_mono ?_).trans hprob
    intro ω hω
    refine ⟨φ, (fun w => (hφ w).1), (fun w => (hφ w).2), hsupp, ?_⟩
    have hi : (∫ w in ball z r, greenFunction (ball z r) y w * φ w ∂S.μ ω) =
        ∫ w, greenFunction (ball z r) y w * φ w ∂S.μ ω := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      simp [greenFunction_of_notMem_right hw]
    rwa [← hi]
  filter_upwards [htail] with ε hε
  have h := (add_le_add (add_le_add hpot (le_refl d)) (le_refl d)).trans hsum
  have h' := hε.trans_lt (h.trans_lt hlt)
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h'

/-- Pointwise convergence of the normalized exit time follows from the Green
kernel convergence, the discrete Dirichlet estimate and Lemma 2.17. -/
theorem pointwise_normalizedExitTime_of_inputs
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    TendstoInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y)
      (fun ω => normalizedExitGreenPotential S r z ω y) :=
  pointwise_normalizedExitTime_of_nearPole 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hy
    (nearPole_small_in_probability 𝒮 h35 h217 hγ hγ2 hρ hρ1 S hS hr hball hy)

end MatedCRT
