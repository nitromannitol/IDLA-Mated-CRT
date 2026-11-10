import MatedCRT.FirstPass.S5d.ClusterFromOdometer
import MatedCRT.FirstPass.S5c.HExclusive

/-!
# Strict compact containment from the point-level inner containment (task fp-S5d-5-1-stopped-repair)

Second route to `StrictClusterCompactContainmentStep` (ClusterInner.lean), which does not use the odometer step
`StrictStoppedOdometerPositivityStep`. The point-level containment `DiscreteClusterInnerBoundStep` (the `Λ^ε_t` form of
Proposition 4.2, `Steps/Sec5/IDLALowerBound.lean`) implies the cell-level statement: if a cell `a` meets `B⁻_s(Λ_t)`, then
`a` is a label of the strict cluster `matedDiscreteCluster`.

Argument: the cell is small (Lemma 2.8, `cellSizeEvent`), so `cell_subset_innerNbhd_half` puts it in `B⁻_{s/2}(Λ_t)`; an
exclusive point `x` of `a` (`exists_exclusive_mem_cell`) lies in it; the point-level containment at depth
`min (s/2) (ρ/2)` puts `x` in a cluster cell `b`, and exclusivity forces `b = a`.

The converse implication is `discreteClusterInnerBound_of_compactContainment` (ClusterInner.lean:44).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The inner neighbourhood `B⁻_δ(X)` decreases as its depth `δ` increases. -/
theorem innerNbhd_mono_depth (X : Set ℂ) {δ δ' : ℝ} (h : δ' ≤ δ) : innerNbhd δ X ⊆ innerNbhd δ' X :=
  fun _ hy => ⟨hy.1, (ENNReal.ofReal_le_ofReal h).trans hy.2⟩

/-- **Strict compact containment (3.1) from the point-level containment.** From the `Λ^ε_t` form of Proposition 4.2
(`DiscreteClusterInnerBoundStep`) and the cell-size estimate (`CellSizeEstimateStmt`), every cell meeting `B⁻_s(Λ_t)` is a
label of the strict cluster, on `{t < T}`, with probability tending to one. -/
theorem strictClusterCompactContainmentStep_of_discreteInner (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) (hD : DiscreteClusterInnerBoundStep 𝒮) :
    StrictClusterCompactContainmentStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ s t hs ht
  have hγ2' : 0 < (2 + γ) ^ 2 := by positivity
  set ζ : ℝ := 1 / (2 + γ) ^ 2 with hζ_def
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ < 1 := by
    rw [hζ_def, div_lt_one hγ2']
    nlinarith
  obtain ⟨p, hp, C, r₀, hr₀, hPoly⟩ := h28 γ hγ hγ2 ζ ρ hζ0 hζ1 hρ hρ1 Ω S hS
  -- the tail of the size event tends to zero (Lemma 2.8)
  have hPolyT : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => C * r ^ p) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (continuous_const.mul (Real.continuous_rpow_const hp.le)).tendsto 0
    rw [Real.zero_rpow hp.ne', mul_zero] at hc
    have hc' : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
    have h := ENNReal.tendsto_ofReal hc'
    rwa [ENNReal.ofReal_zero] at h
  have hZT : Tendsto (fun ε => S.P (cellSizeEvent S γ ζ ρ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPolyT
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr₀)] with ε hε hεr
    exact hPoly ε hε hεr
  -- the Lemma 2.8 bound is eventually below `s/2`
  have hb : 0 < 2 / (2 + γ) ^ 2 - ζ := by
    have h : 2 / (2 + γ) ^ 2 - ζ = ζ := by rw [hζ_def]; ring
    rw [h]; exact hζ0
  have hsmall : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ (2 / (2 + γ) ^ 2 - ζ))) :=
      (Real.continuous_rpow_const hb.le).tendsto 0
    rw [Real.zero_rpow hb.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hev_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - ζ) < s / 2 :=
    hsmall.eventually (gt_mem_nhds (by linarith))
  -- almost surely: the cells are the area parametrization and `Λ` is monotone
  have hgood : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) :=
    hS.isAreaParametrized.and (hΛ.mono fun ω h => h.2.1.monotoneOn)
  have hN : S.P {ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} = 0 :=
    ae_iff.1 hgood
  -- the point-level containment at depth `δ = min (s/2) (ρ/2)`
  set δ : ℝ := min (s / 2) (ρ / 2) with hδ_def
  have hδ0 : 0 < δ := lt_min (half_pos hs) (half_pos hρ)
  have hδρ : δ < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have hD' := hD γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ0 hδρ ht
  refine tendsToOneOn_of_good_cover hD' hZT hN ?_
  filter_upwards [hev_small, eventually_mem_nhdsWithin] with ε hεs hε0
  have hε : (0 : ℝ) < ε := hε0
  intro ω hωF hωN hωZ hωE'
  have hap := not_not.mp hωN
  have hΛball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime hρ hap.2 ht hωF
  intro a ha
  obtain ⟨y, hyc, hyK⟩ := ha
  have hcellmeet : (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := ⟨y, hyc, hΛball hyK.1⟩
  obtain ⟨hlo, hup⟩ := hωZ a hcellmeet
  have hdiam : diam (cell ε (S.η ω) a) ≤ s / 2 := hup.trans hεs.le
  have hbd : Bornology.IsBounded (cell ε (S.η ω) a) := by
    by_contra hunb
    rw [Metric.diam_eq_zero_of_unbounded hunb] at hlo
    have : 0 < ε ^ (2 / (2 - γ) ^ 2 + ζ) := Real.rpow_pos_of_pos hε _
    linarith
  -- the cell lies in `B⁻_{s/2}(Λ_t)`, and so does an exclusive point of it
  have hsub : cell ε (S.η ω) a ⊆ innerNbhd (s / 2) (Λ ω t) :=
    cell_subset_innerNbhd_half hs hbd hdiam ⟨y, hyc, hyK⟩
  obtain ⟨x, hxa, hex⟩ := MatedCRT.S5c.exists_exclusive_mem_cell hap.1 hε a
  have hxδ : x ∈ innerNbhd δ (Λ ω t) := innerNbhd_mono_depth (Λ ω t) (min_le_left (s / 2) (ρ / 2)) (hsub hxa)
  have hxF : x ∈ fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) := hωE' hxδ
  simp only [fillCells, mem_iUnion] at hxF
  obtain ⟨b, hb', hxb⟩ := hxF
  rw [hex b hxb] at hb'
  exact hb'

end MatedCRT
