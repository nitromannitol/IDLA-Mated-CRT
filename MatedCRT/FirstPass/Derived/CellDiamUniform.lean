import MatedCRT.FirstPass.Derived.InterpKernelVertex
import MatedCRT.FirstPass.Derived.CellDiameterEvent
import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto

/-!
# Large cell diameters: the events and their hypotheses

For a proper onto curve `η`, the largest diameter of the cells meeting a ball is finite.  This file
packages the family of events `A_n(δ) = {ω : η'(ω) proper onto, (ofReal δ)⁻¹ < diam^{ε_n}_R(η'(ω))}`
(`δ > 0`; for `δ ≤ 0` the threshold is `⊤` and the event is empty) as a family of null-measurable
events that increases with the scale `δ`, has empty intersection over `δ > 0` for every `n`, and is
eventually of probability at most any prescribed `c > 0` at the scale `δ = 1`
(`MatedCRT.CellDiameterEvent.tendsto_prob_maxCellDiam_nhdsWithin`).  These are exactly the hypotheses
of the passage from large indices to all indices.

* `properCurveSet`, `ae_mem_properCurveSet`: the almost sure properness of `η'`;
* `maxCellDiam_lt_top_of_mem_properCurveSet`;
* `cellDiamBig`, `measurableSet_cellDiamBig`, `nullMeasurableSet_cellDiamBig`,
  `cellDiamBig_mono`, `iInter_cellDiamBig_eq_empty`, `eventually_prob_cellDiamBig_le`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The curves `η'(ω)` that are proper (tend to infinity at infinity) and onto. -/
def properCurveSet (η' : Ω → C(ℝ, ℂ)) : Set Ω :=
  {ω | Tendsto (⇑(η' ω)) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective (η' ω)}

/-- Almost surely the curve is proper and onto. -/
theorem ae_mem_properCurveSet {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ω ∈ properCurveSet η' := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hae] with ω hap hcoc hω
  refine ⟨?_, ?_⟩
  · rw [hω]
    exact hcoc
  · intro z
    obtain ⟨t, ht⟩ := hap.2.2.1 z
    exact ⟨t, by rw [show ⇑(η' ω) = S.η ω from hω]; exact ht⟩

theorem nullMeasurableSet_properCurveSet {μ : Measure Ω} {η' : Ω → C(ℝ, ℂ)}
    (h : ∀ᵐ ω ∂μ, ω ∈ properCurveSet η') : NullMeasurableSet (properCurveSet η') μ :=
  (NullMeasurableSet.of_null (ae_iff.1 h)).of_compl

omit [MeasurableSpace Ω] in
/-- On a proper onto curve the largest cell diameter in a ball is finite. -/
theorem maxCellDiam_lt_top_of_mem_properCurveSet {η' : Ω → C(ℝ, ℂ)} {ω : Ω}
    (hω : ω ∈ properCurveSet η') {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    maxCellDiam ε (⇑(η' ω)) R < ⊤ :=
  maxCellDiam_lt_top_of_proper hε hω.1 hω.2 R

/-- The event that the cell diameters in the ball `B_R` exceed `(ofReal δ)⁻¹`, on the set where the
curve is proper and onto.  It increases with `δ`; for `δ ≤ 0` it is empty. -/
def cellDiamBig (η' : Ω → C(ℝ, ℂ)) (ε R δ : ℝ) : Set Ω :=
  {ω | ω ∈ properCurveSet η' ∧ (ENNReal.ofReal δ)⁻¹ < maxCellDiam ε (⇑(η' ω)) R}

theorem measurableSet_diamBig {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (ε R δ : ℝ) :
    MeasurableSet {ω | (ENNReal.ofReal δ)⁻¹ < maxCellDiam ε (⇑(η' ω)) R} := by
  by_cases hδ : 0 < δ
  · have h1 : (ENNReal.ofReal δ)⁻¹ = ENNReal.ofReal δ⁻¹ := (ENNReal.ofReal_inv_of_pos hδ).symm
    simp only [h1]
    exact (isOpen_setOf_ofReal_lt_maxCellDiam ε R (inv_nonneg.2 hδ.le)).measurableSet.preimage hη'
  · have h0 : ENNReal.ofReal δ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hδ)
    simp only [h0, ENNReal.inv_zero]
    have : {ω | (⊤ : ℝ≥0∞) < maxCellDiam ε (⇑(η' ω)) R} = ∅ := by
      ext ω
      simp
    rw [this]
    exact MeasurableSet.empty

theorem nullMeasurableSet_cellDiamBig {μ : Measure Ω} {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (h : ∀ᵐ ω ∂μ, ω ∈ properCurveSet η') (ε R δ : ℝ) :
    NullMeasurableSet (cellDiamBig η' ε R δ) μ :=
  (nullMeasurableSet_properCurveSet h).inter (measurableSet_diamBig hη' ε R δ).nullMeasurableSet

omit [MeasurableSpace Ω] in
theorem cellDiamBig_mono (η' : Ω → C(ℝ, ℂ)) (ε R : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    cellDiamBig η' ε R δ ⊆ cellDiamBig η' ε R δ' := by
  rintro ω ⟨hω, hlt⟩
  exact ⟨hω, lt_of_le_of_lt (ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal h)) hlt⟩

omit [MeasurableSpace Ω] in
/-- For a proper onto curve, the cell diameters in a ball are not above every threshold. -/
theorem iInter_cellDiamBig_eq_empty (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (⋂ δ > (0 : ℝ), cellDiamBig η' ε R δ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
  simp only [mem_iInter] at hω
  have hlt := maxCellDiam_lt_top_of_mem_properCurveSet (hω 1 one_pos).1 hε R
  set M := maxCellDiam ε (⇑(η' ω)) R with hM
  have hδ : 0 < (M.toReal + 1)⁻¹ := by positivity
  have h2 := (hω _ hδ).2
  rw [← ENNReal.ofReal_inv_of_pos hδ, inv_inv] at h2
  have h3 : M ≤ ENNReal.ofReal (M.toReal + 1) :=
    calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hlt.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  exact absurd h2 (not_lt.2 h3)

/-- At the scale `δ = 1`, the event of large cell diameters is eventually of probability at most `c`. -/
theorem eventually_prob_cellDiamBig_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) (R : ℝ) {c : ℝ≥0∞}
    (hc : 0 < c) : ∀ᶠ n in atTop, S.P (cellDiamBig η' (eps n) R 1) ≤ c := by
  have hεn : Tendsto eps atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have h := (tendsto_order.1 ((MatedCRT.CellDiameterEvent.tendsto_prob_maxCellDiam_nhdsWithin hS hae
    R 1 one_pos).comp hεn)).2 c hc
  filter_upwards [h] with n hn
  refine le_trans (measure_mono ?_) hn.le
  rintro ω ⟨-, hlt⟩
  simpa using hlt

end MatedCRT.FirstPass.Derived
