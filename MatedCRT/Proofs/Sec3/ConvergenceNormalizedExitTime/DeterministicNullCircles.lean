import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CompactMassMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenSumMeasurable

/-! # Deterministic null circles for random LQG measure -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- On a bounded interval of radii, only countably many deterministic circles
can have positive LQG mass with positive probability. -/
theorem MatedCRTEnv.IsValid.countable_nonae_null_spheres
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (y : ℂ) (R : ℝ) :
    {r : Icc (0 : ℝ) R | ¬ ∀ᵐ ω ∂S.P, S.μ ω (sphere y r) = 0}.Countable := by
  classical
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let I := Icc (0 : ℝ) R
  let g : I → Ω → ℝ≥0∞ := fun r ω =>
    S.μ ω (sphere y r) / (1 + S.μ ω (closedBall y R))
  have hg (r : I) : AEMeasurable (g r) S.P := by
    exact (hS.aemeasurable_lqg_compact_mass_ennreal (isCompact_sphere y r)).div
      (aemeasurable_const.add (hS.aemeasurable_lqg_compact_mass_ennreal (isCompact_closedBall y R)))
  have hsum (F : Finset I) : ∀ᵐ ω ∂S.P, ∑ r ∈ F, g r ω ≤ 1 := by
    filter_upwards [hS.isLQGMeasure] with ω hμ
    let _ : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
    have hdisj : PairwiseDisjoint (↑F : Set I) (fun r => sphere y (r : ℝ)) := by
      intro a ha b hb hab
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      apply hab
      apply Subtype.ext
      exact (mem_sphere.mp hxa).symm.trans (mem_sphere.mp hxb)
    have hsubset : (⋃ r ∈ F, sphere y (r : ℝ)) ⊆ closedBall y R := by
      intro x hx
      obtain ⟨r, _, hr⟩ := mem_iUnion₂.mp hx
      rw [mem_closedBall, mem_sphere] at *
      exact hr.le.trans r.property.2
    have hmass : (∑ r ∈ F, S.μ ω (sphere y (r : ℝ))) ≤ S.μ ω (closedBall y R) := by
      rw [← measure_biUnion_finset hdisj (fun _ _ => isClosed_sphere.measurableSet)]
      exact measure_mono hsubset
    calc
      (∑ r ∈ F, g r ω) = (∑ r ∈ F, S.μ ω (sphere y (r : ℝ))) /
          (1 + S.μ ω (closedBall y R)) := by simp [g, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ S.μ ω (closedBall y R) / (1 + S.μ ω (closedBall y R)) :=
        ENNReal.div_le_div_right hmass _
      _ ≤ 1 := by
        exact (ENNReal.div_le_div_right (le_add_left le_rfl) _).trans ENNReal.div_self_le_one
  let v : I → ℝ≥0∞ := fun r => ∫⁻ ω, g r ω ∂S.P
  have hv : (∑' r : I, v r) ≤ 1 := by
    apply ENNReal.summable.tsum_le_of_sum_le
    intro F
    rw [← lintegral_finsetSum' F (fun r _ => hg r)]
    calc
      (∫⁻ ω, ∑ r ∈ F, g r ω ∂S.P) ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂S.P :=
        lintegral_mono_ae (hsum F)
      _ = 1 := by simp
  have hc : v.support.Countable := Summable.countable_support_ennreal (ne_of_lt (hv.trans_lt (by simp)))
  apply hc.mono
  intro r hr
  change v r ≠ 0
  intro hv0
  have hzero := (lintegral_eq_zero_iff' (hg r)).mp hv0
  apply hr
  filter_upwards [hzero, hS.isLQGMeasure] with ω hzeroω hμ
  let _ : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  have hden : 1 + S.μ ω (closedBall y R) ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (isCompact_closedBall y R).measure_lt_top.ne⟩
  exact (ENNReal.div_eq_zero_iff).mp hzeroω |>.resolve_right hden

/-- Every positive radius contains a smaller deterministic radius whose
circle has zero LQG mass almost surely. -/
theorem MatedCRTEnv.IsValid.exists_ae_null_sphere
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (y : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ᵐ ω ∂S.P, S.μ ω (sphere y r) = 0 := by
  classical
  let B : Set ℝ := Subtype.val '' {r : Icc (0 : ℝ) R |
    ¬ ∀ᵐ ω ∂S.P, S.μ ω (sphere y r) = 0}
  have hB : B.Countable := (hS.countable_nonae_null_spheres y R).image Subtype.val
  have hmeasure := measure_sdiff_null (s := Ioo (0 : ℝ) R) (hB.measure_zero volume)
  have hpos : 0 < volume (Ioo (0 : ℝ) R \ B) := by
    rw [hmeasure, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨r, hr, hrB⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨r, hr.1, hr.2, ?_⟩
  by_contra hbad
  apply hrB
  exact ⟨⟨r, hr.1.le, hr.2.le⟩, hbad, rfl⟩

/-- Lemma 3.3 yields convergence in probability of truncated Green sums
for a deterministic truncation radius chosen arbitrarily small. -/
theorem exists_greenSum_tendstoInProbability_fixed_truncation
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r R : ℝ} {z y : ℂ} (hr : 0 < r) (hR : 0 < R)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ δ + dist y z < r ∧
      TendstoInProbability S.P
        (fun e ω => (S.mε e)⁻¹ * ∑ a ∈ truncatedGreenCells e (S.η ω) z y r δ,
          greenKernel (S.mult e ω) (interiorCellVertices e (S.η ω) (ball z r))
            (vertexOf e (S.η ω) y) a)
        (fun ω => ∫ x in ball z r \ ball y δ,
          (S.c₀ / 6) * HarmonicBalls.greenFunction (ball z r) y x ∂S.μ ω) := by
  have hy' : dist y z < r := mem_ball.mp hy
  have hp : 0 < min R (r - dist y z) := lt_min hR (by linarith)
  obtain ⟨δ, hδ, hδsmall, hcircle⟩ := hS.exists_ae_null_sphere y hp
  have hδR : δ < R := hδsmall.trans_le (min_le_left _ _)
  have hsmall : δ + dist y z < r := by
    have := hδsmall.trans_le (min_le_right R (r - dist y z))
    linarith
  exact ⟨δ, hδ, hδR, hsmall,
    greenSum_tendstoInProbability_fixed_truncation 𝒮 h33 hγ hγ2 hρ hρ1 S hS
      hr hδ hball hy hsmall hcircle⟩

end MatedCRT
