import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Almost sure subsequences for uniform convergence in probability -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal UniformConvergence

/-- Uniform convergence in probability is convergence in measure for the
extended metric of uniform convergence on the restricted domain. -/
theorem tendstoInMeasure_uniformFun_of_uniformInProbability
    {Ω α : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Set α)
    (F : ℝ → Ω → α → ℝ) (g : α → ℝ)
    (hconv : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ x ∈ D, δ < ‖F ε ω x - g x‖})
        (𝓝[>] 0) (𝓝 0)) :
    TendstoInMeasure P (fun ε ω => UniformFun.ofFun (fun x : D => F ε ω x))
      (𝓝[>] 0) (fun _ => UniformFun.ofFun (fun x : D => g x)) := by
  let U : ℝ → Ω → (D →ᵤ ℝ) := fun ε ω => UniformFun.ofFun (fun x => F ε ω x)
  let v : Ω → (D →ᵤ ℝ) := fun _ => UniformFun.ofFun (fun x => g x)
  have hU : TendstoInMeasure P U (𝓝[>] 0) v := by
    apply tendstoInMeasure_of_ne_top
    intro t ht httop
    let d : ℝ := t.toReal / 2
    have hd : 0 < d := half_pos (ENNReal.toReal_pos ht.ne' httop)
    have hdt : ENNReal.ofReal d < t := by
      have heq : ENNReal.ofReal t.toReal = t := ENNReal.ofReal_toReal httop
      calc
        ENNReal.ofReal d < ENNReal.ofReal t.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos ht.ne' httop)).2
            (by dsimp [d]; linarith [ENNReal.toReal_pos ht.ne' httop])
        _ = t := heq
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv d hd)
      (fun _ => zero_le)
    intro ε
    apply measure_mono
    intro ω hω
    by_contra hn
    have hbound : edist (U ε ω) (v ω) ≤ ENNReal.ofReal d := by
      rw [UniformFun.edist_le]
      intro x
      have hx : ‖F ε ω x - g x‖ ≤ d := le_of_not_gt (fun h => hn ⟨x, x.property, h⟩)
      simpa [U, v, edist_dist, Real.dist_eq, Real.norm_eq_abs] using
        (ENNReal.ofReal_le_ofReal hx)
    exact (not_le_of_gt (lt_of_le_of_lt hbound hdt)) hω
  exact hU

/-- Every deterministic mesh sequence tending to zero has a further
subsequence along which convergence is almost surely uniform. Failure events
need not be measurable. -/
theorem exists_ae_uniform_subsequence_along
    {Ω α : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Set α)
    (F : ℝ → Ω → α → ℝ) (g : α → ℝ)
    (hconv : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ x ∈ D, δ < ‖F ε ω x - g x‖})
        (𝓝[>] 0) (𝓝 0)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n => F (ε (ns n)) ω) g atTop D := by
  have hU := (tendstoInMeasure_uniformFun_of_uniformInProbability P D F g hconv).comp hε
  obtain ⟨ns, hns, hae⟩ := hU.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with ω hω
  have hu := UniformFun.tendsto_iff_tendstoUniformly.1 hω
  exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).2 hu

/-- Uniform convergence in probability on a fixed set admits an almost surely
uniformly convergent subsequence. -/
theorem exists_ae_uniform_subsequence_of_uniformInProbability
    {Ω α : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Set α)
    (F : ℝ → Ω → α → ℝ) (g : α → ℝ)
    (hconv : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ x ∈ D, δ < ‖F ε ω x - g x‖})
        (𝓝[>] 0) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] 0) ∧
      ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n => F (ε n) ω) g atTop D := by
  obtain ⟨ε, hε, hae⟩ :=
    (tendstoInMeasure_uniformFun_of_uniformInProbability P D F g hconv).exists_seq_tendsto_ae'
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hae] with ω hω
  have hu := UniformFun.tendsto_iff_tendstoUniformly.1 hω
  exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).2 hu

/-- Lemma 3.3 admits a deterministic mesh subsequence along which the
rescaled Green kernels converge almost surely and uniformly away from the pole. -/
theorem greenKernel_ae_uniform_subsequence_away_from_pole
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (D : Set ℂ) (hD : D ⊆ closedBall z r \ {y}) (hdist : 0 < infDist y D) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] 0) ∧ ∀ᵐ ω ∂S.P,
      TendstoUniformlyOn (fun n => rescale (S.mε (ε n)) (ε n) (S.η ω)
        (fun a => (ε n)⁻¹ * greenKernel (S.mult (ε n) ω)
          (interiorCellVertices (ε n) (S.η ω) (ball z r)) (vertexOf (ε n) (S.η ω) y) a))
        (fun x => (S.c₀ / 6) * greenFunction (ball z r) y x) atTop D := by
  refine exists_ae_uniform_subsequence_of_uniformInProbability S.P D
    (fun ε ω => rescale (S.mε ε) ε (S.η ω)
      (fun a => ε⁻¹ * greenKernel (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) a))
    (fun x => (S.c₀ / 6) * greenFunction (ball z r) y x) ?_
  intro δ hδ
  have h := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy δ hδ D hD hdist
  simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le, exists_prop,
    Real.norm_eq_abs] using h

end MatedCRT
