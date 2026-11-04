import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FixedTruncation
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.UniformSubsequence

/-! # Green sums over cells away from the pole -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal

/-- The finite collection of cells inside the outer ball and avoiding the
pole ball. If the collection is not finite, the value is empty. -/
noncomputable def truncatedGreenCells (ε : ℝ) (η : ℝ → ℂ)
    (z y : ℂ) (r δ : ℝ) : Finset ℤ := by
  classical
  exact if h : (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)).Finite
    then h.toFinset else ∅

/-- Properness makes the truncated cell collection finite at positive mesh. -/
theorem coe_truncatedGreenCells {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε : ℝ} (hε : 0 < ε)
    (z y : ℂ) (r δ : ℝ) :
    (truncatedGreenCells ε η z y r δ : Set ℤ) =
      interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ) := by
  classical
  have hfin : (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)).Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset
      (sdiff_subset.trans (by unfold interiorCellVertices; exact sdiff_subset))
  rw [truncatedGreenCells, dite_eq_left hfin]
  exact Set.Finite.coe_toFinset hfin

/-- A small puncture leaves a nonempty set at positive distance from its pole. -/
theorem infDist_punctured_ball_pos {z y : ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ + dist y z < r) : 0 < infDist y (ball z r \ ball y δ) := by
  have hwy : dist (y + (δ : ℂ)) y = δ := by
    simp [dist_eq_norm, abs_of_pos hδ]
  have hnonempty : (ball z r \ ball y δ).Nonempty := by
    refine ⟨y + (δ : ℂ), ?_, ?_⟩
    · rw [mem_ball]
      exact (dist_triangle _ y z).trans_lt (by linarith)
    · rw [mem_ball, hwy]
      exact lt_irrefl δ
  have hbound : δ ≤ infDist y (ball z r \ ball y δ) := (le_infDist hnonempty).2 (by
    intro x hx
    rw [dist_comm]
    exact not_lt.mp hx.2)
  exact hδ.trans_le hbound

/-- For almost every environment, at most countably many concentric circles
have positive LQG mass. The exceptional radii may depend on the environment. -/
theorem MatedCRTEnv.IsValid.ae_countable_positive_circle_masses
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (y : ℂ) :
    ∀ᵐ ω ∂S.P, {δ : ℝ | 0 < S.μ ω (sphere y δ)}.Countable := by
  filter_upwards [hS.isLQGMeasure] with ω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  have h := Measure.countable_meas_level_set_pos (μ := S.μ ω)
    (continuous_id.dist continuous_const : Continuous (fun x : ℂ => dist x y)).measurable
  simpa only [sphere, id_eq] using h

/-- Along any mesh sequence, Lemma 3.3 identifies a further subsequential
limit of truncated Green sums when the truncation circle has zero mass. -/
theorem greenSum_ae_subsequence_fixed_truncation
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hsmall : δ + dist y z < r)
    (hcircle : ∀ᵐ ω ∂S.P, S.μ ω (sphere y δ) = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂S.P,
      Tendsto (fun n => (S.mε (ε (ns n)))⁻¹ *
        ∑ a ∈ truncatedGreenCells (ε (ns n)) (S.η ω) z y r δ,
          greenKernel (S.mult (ε (ns n)) ω)
            (interiorCellVertices (ε (ns n)) (S.η ω) (ball z r))
            (vertexOf (ε (ns n)) (S.η ω) y) a) atTop
        (𝓝 (∫ x in ball z r \ ball y δ,
          (S.c₀ / 6) * greenFunction (ball z r) y x ∂S.μ ω)) := by
  let D := ball z r \ ball y δ
  have hdist : 0 < infDist y D := infDist_punctured_ball_pos hδ hsmall
  have hD : D ⊆ closedBall z r \ {y} := by
    intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    intro hxy
    have : x = y := mem_singleton_iff.mp hxy
    subst x
    exact hx.2 (mem_ball_self hδ)
  have hDρ : D ⊆ ball 0 ρ := sdiff_subset.trans hball
  let F : ℝ → Ω → ℂ → ℝ := fun e ω => rescale (S.mε e) e (S.η ω)
    (fun a => e⁻¹ * greenKernel (S.mult e ω)
      (interiorCellVertices e (S.η ω) (ball z r)) (vertexOf e (S.η ω) y) a)
  let g : ℂ → ℝ := fun x => (S.c₀ / 6) * greenFunction (ball z r) y x
  have hprob : ∀ t : ℝ, 0 < t →
      Tendsto (fun e => S.P {ω | ∃ x ∈ D, t < ‖F e ω x - g x‖})
        (𝓝[>] 0) (𝓝 0) := by
    intro t ht
    have h := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy t ht D hD hdist
    simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le,
      exists_prop, Real.norm_eq_abs, F, g] using h
  obtain ⟨ns, hns, hconv⟩ := exists_ae_uniform_subsequence_along S.P D F g hprob ε hε
  refine ⟨ns, hns, ?_⟩
  have he : Tendsto (ε ∘ ns) atTop (𝓝[>] 0) := hε.comp hns.tendsto_atTop
  have hint := greenFunction_ae_integrableOn_away_from_pole 𝒮 h33 hγ hγ2 hρ hρ1
    S hS hr hball hy D hD hDρ hdist
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hcircle, hint, hconv]
    with ω harea hp hc hi hu
  let l : Filter ℝ := Filter.map (ε ∘ ns) atTop
  have hl : l ≤ 𝓝[>] (0 : ℝ) := he
  have hF : ∀ᶠ e in l, (truncatedGreenCells e (S.η ω) z y r δ : Set ℤ) =
      interiorCellVertices e (S.η ω) (ball z r) \ cellVertices e (S.η ω) (ball y δ) := by
    filter_upwards [hl self_mem_nhdsWithin] with e hepos
    exact coe_truncatedGreenCells harea.1 hp hepos z y r δ
  have hu' : TendstoUniformlyOn (fun e => F e ω) g l D := by
    simpa only [TendstoUniformlyOn, l, Filter.eventually_map, Function.comp_def] using hu
  have hsum := tendsto_fixed_truncated_vertex_sum harea hp z y r δ hc hi l hl
    (fun e => truncatedGreenCells e (S.η ω) z y r δ) S.mε
    (fun e a => greenKernel (S.mult e ω) (interiorCellVertices e (S.η ω) (ball z r))
      (vertexOf e (S.η ω) y) a) hF hu'
  exact hsum

end MatedCRT
