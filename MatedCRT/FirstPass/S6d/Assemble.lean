import MatedCRT.FirstPass.S6d.Core68

/-!
# FIRST PASS: probability and cell helpers for the localization of Lemma 6.8

`ProbTendsToOne` bookkeeping (eventual inclusion, intersection, almost sure sets), the eventual smallness of powers
`ε^c` as `ε → 0⁺`, and the cell facts used by `firstPass_6_8_faithful` (FirstPass/S6d.lean).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Eventual inclusion: if `E ε ⊆ F ε` for all small `ε`, then `P(F ε)ᶜ → 0` as well. -/
theorem loc_pt_mono_ev {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : ProbTendsToOne P E) (hEF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), E ε ⊆ F ε) : ProbTendsToOne P F := by
  unfold ProbTendsToOne at *
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [hEF] with ε hε
    exact measure_mono (compl_subset_compl.2 hε)

/-- Intersection of two events of probability tending to one. -/
theorem loc_pt_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : ProbTendsToOne P E) (hF : ProbTendsToOne P F) : ProbTendsToOne P fun ε => E ε ∩ F ε := by
  unfold ProbTendsToOne at *
  have hsum : Tendsto (fun ε => P (E ε)ᶜ + P (F ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hE.add hF
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · exact Eventually.of_forall fun ε => by
      calc P (E ε ∩ F ε)ᶜ = P ((E ε)ᶜ ∪ (F ε)ᶜ) := by rw [compl_inter]
        _ ≤ P (E ε)ᶜ + P (F ε)ᶜ := measure_union_le _ _

/-- An almost sure event gives a constant event of probability tending to one. -/
theorem loc_pt_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Set Ω}
    (hG : ∀ᵐ ω ∂P, ω ∈ G) : ProbTendsToOne P fun _ => G := by
  unfold ProbTendsToOne
  have h0 : P Gᶜ = 0 := ae_iff.1 hG
  simp only [h0]
  exact tendsto_const_nhds

/-- `ε ^ c < K` for small `ε > 0`, when `c > 0`. -/
theorem loc_eventually_rpow_lt {c : ℝ} (hc : 0 < c) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ c < K := by
  have h1 : Tendsto (fun ε : ℝ => ε ^ c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow hc.ne'] using
      ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto).mono_left nhdsWithin_le_nhds
  exact (tendsto_order.1 h1).2 K hK

/-- If `ε ^ (p - q) < 1 / K`, then `K * ε ^ p < ε ^ q` (`ε > 0`). -/
theorem loc_mul_rpow_lt {ε p q K : ℝ} (hε : 0 < ε) (hK : 0 < K) (hc : ε ^ (p - q) < 1 / K) :
    K * ε ^ p < ε ^ q := by
  have hsplit : ε ^ p = ε ^ q * ε ^ (p - q) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have hKc : K * ε ^ (p - q) < 1 := by
    have := mul_lt_mul_of_pos_left hc hK
    rwa [mul_one_div_cancel hK.ne'] at this
  have hq : 0 < ε ^ q := Real.rpow_pos_of_pos hε q
  calc K * ε ^ p = ε ^ q * (K * ε ^ (p - q)) := by rw [hsplit]; ring
    _ < ε ^ q * 1 := mul_lt_mul_of_pos_left hKc hq
    _ = ε ^ q := mul_one _

/-- The fill of the augmented set, as a set of vertices: the localized vertex set `V(B_t(Ē ∪ C))` splits into the two
localized sets. -/
theorem cellVertices_thick_fill_insert (ε : ℝ) (η : ℝ → ℂ) (a : ℤ) (Θ : Set ℤ) (t : ℝ) :
    cellVertices ε η (thickening t (fillCells ε η (insert a Θ))) =
      cellVertices ε η (thickening t (cell ε η a)) ∪ cellVertices ε η (thickening t (fillCells ε η Θ)) := by
  rw [fillCells_insert_eq, Metric.thickening_union, cellVertices_union_eq]

/-- Monotonicity of the vertex set in the domain. -/
theorem cellVertices_mono_set (ε : ℝ) (η : ℝ → ℂ) {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ hk => hk.mono (inter_subset_inter_right _ h)

/-- A cell is bounded when `η` is continuous. -/
theorem cell_bounded_of_continuous {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) :
    ∀ k : ℤ, Bornology.IsBounded (cell ε η k) :=
  fun _ => (isCompact_Icc.image hη).isBounded

/-- A diameter bound on a bounded cell gives the pointwise bound used in `loc_core`. -/
theorem dist_le_of_diam_le {ε d : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {v : ℤ}
    (hdiam : diam (cell ε η v) ≤ d) : ∀ x ∈ cell ε η v, ∀ y ∈ cell ε η v, dist x y ≤ d :=
  fun _ hx _ hy => (dist_le_diam_of_mem (cell_bounded_of_continuous hη v) hx hy).trans hdiam

end MatedCRT
