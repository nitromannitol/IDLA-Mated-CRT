import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.FirstPass.Derived.LimLimSmall

/-!
# The cell-diameter event is negligible as `ε → 0` for every fixed scale `δ`

For a valid environment, the cells of the space-filling curve meeting a fixed disk have diameter at
most any fixed `d > 0` with probability tending to `1` as the mesh `ε → 0⁺`
(`MatedCRT.FirstPass.Derived.hdiam_of_isValid`, along sequences).  Here this is turned into

* `cell_dist_le_of_maxCellDiam_le`: a deterministic bound `maxCellDiam ε η (ρ₁ - 1) ≤ d` for a continuous
  curve gives the pointwise bound `dist x y ≤ d` for all points `x, y` of a cell meeting `B_{ρ₁}`
  (the form used as `hdiam` in the good-environment exit coupling);
* `tendsto_prob_maxCellDiam_nhdsWithin`: the sequential statement along the filter `𝓝[>] 0`;
* `limLimSmall_cellDiam`: for every scale function `d δ > 0` the failure event of `hdiam` is
  `LimLimSmall` in `ε → 0` and then `δ → 0` (indeed for each fixed `δ` it vanishes as `ε → 0⁺`).
-/

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT
namespace CellDiameterEvent

open MatedCRT.FirstPass.Derived (maxCellDiam hdiam_of_isValid)

/-- A continuous curve whose cells meeting `B_{ρ₁}` have `maxCellDiam ≤ d` has `dist x y ≤ d` for all
points `x, y` of such a cell. -/
theorem cell_dist_le_of_maxCellDiam_le {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {ρ₁ d : ℝ}
    (hd : 0 ≤ d) (h : maxCellDiam ε η (ρ₁ - 1) ≤ ENNReal.ofReal d) :
    ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ₁).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d := by
  intro k hk x hx y hy
  have hk' : (cell ε η k ∩ ball (0 : ℂ) (ρ₁ - 1 + 1)).Nonempty := by rwa [sub_add_cancel]
  have h1 : ENNReal.ofReal (Metric.diam (cell ε η k)) ≤ ENNReal.ofReal d :=
    le_trans (le_iSup₂_of_le k hk' le_rfl) h
  have h2 : Metric.diam (cell ε η k) ≤ d := (ENNReal.ofReal_le_ofReal_iff hd).1 h1
  have hb : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  exact (Metric.dist_le_diam_of_mem hb hx hy).trans h2

/-- The sequential convergence in probability of the maximal cell diameter, along `ε → 0⁺`. -/
theorem tendsto_prob_maxCellDiam_nhdsWithin {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) (R a : ℝ) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  exact hdiam_of_isValid hS hae (tendsto_nhdsWithin_iff.1 hu).1 R a ha

/-- **The cell-diameter event is negligible**: for every valid environment, every radius `ρ₁` and every
scale function `d δ > 0`, the event that some cell meeting `B_{ρ₁}` has two points at distance `> d δ`
is `LimLimSmall` (as `ε → 0` and then `δ → 0`). -/
theorem limLimSmall_cellDiam {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) (ρ₁ : ℝ) {d : ℝ → ℝ} (hd : ∀ δ : ℝ, 0 < δ → 0 < d δ) :
    LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ k : ℤ,
      (cell ε (⇑(η' ω)) k ∩ ball (0 : ℂ) ρ₁).Nonempty →
        ∀ x ∈ cell ε (⇑(η' ω)) k, ∀ y ∈ cell ε (⇑(η' ω)) k, dist x y ≤ d δ}) := by
  refine LimLimSmall.of_tendsto_eps fun δ hδ _ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_prob_maxCellDiam_nhdsWithin hS hae (ρ₁ - 1) (d δ) (hd δ hδ)) (fun _ => zero_le)
    (fun ε => measure_mono ?_)
  intro ω hω
  by_contra hne
  exact hω (cell_dist_le_of_maxCellDiam_le (η' ω).continuous (hd δ hδ).le (not_lt.1 hne))

end CellDiameterEvent
end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.CellDiameterEvent.cell_dist_le_of_maxCellDiam_le
#print axioms MatedCRT.CellDiameterEvent.limLimSmall_cellDiam
