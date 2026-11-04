import MatedCRT.Draft.Section5

/-!
# Proposition 5.1: deterministic and measure-theoretic tools

* `innerNbhd_subset_fillCells_deep`: if `B⁻_{δ/2}(X) ⊆ L̄` (the union of the cells of `L`) and every cell of `L` meets
  `B_ρ` and has diameter `< δ/4`, then `B⁻_δ(X)` is covered by the cells of the vertices `a ∈ L` with
  `dist(η(a), ∂L̄) > δ/4` (the cell-size step of the proof of Proposition 5.1, lines 2034-2045).
* `annealedOuterProb_le_add`: if the sections of `E` are contained in those of `E₁` off a set `B` of environments,
  then the annealed outer probability of `E` is at most that of `E₁` plus `P*(B)`.
-/

namespace MatedCRT

namespace IDLALowerBound

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- `η(a)` lies in the cell `H^ε_a = η([a - ε, a])`. -/
theorem vertexPoint_mem_cell' {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

theorem fillCells_mono' {ε : ℝ} {η : ℝ → ℂ} {A A' : Set ℤ} (h : A ⊆ A') : fillCells ε η A ⊆ fillCells ε η A' :=
  biUnion_subset_biUnion_left h

/-- The inner neighbourhood is antitone in the width. -/
theorem innerNbhd_anti {δ δ' : ℝ} (h : δ' ≤ δ) (X : Set ℂ) : innerNbhd δ X ⊆ innerNbhd δ' X :=
  fun _ hx => ⟨hx.1, (ENNReal.ofReal_le_ofReal h).trans hx.2⟩

/-- A point of `B⁻_δ(X)` is at distance at least `δ` from `Xᶜ`. -/
theorem le_dist_of_mem_innerNbhd {δ : ℝ} {X : Set ℂ} {x : ℂ} (hx : x ∈ innerNbhd δ X) {w : ℂ} (hw : w ∉ X) :
    δ ≤ dist x w := by
  have h := hx.2.trans (infEDist_le_edist_of_mem (show w ∈ Xᶜ from hw))
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h

/-- **The cell-size step of Proposition 5.1** (lines 2034-2045): if `B⁻_{δ/2}(X) ⊆ L̄` and every cell of a vertex of
`L` is bounded, meets `B_ρ` and has diameter `< δ/4`, then `B⁻_δ(X)` is covered by the cells of the vertices
`a ∈ L` with `dist(η(a), ∂L̄) > δ/4`. -/
theorem innerNbhd_subset_fillCells_deep {ε δ ρ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) {η : ℝ → ℂ} {L : Set ℤ}
    {X : Set ℂ} (hb : ∀ a ∈ L, Bornology.IsBounded (cell ε η a)) (hd : ∀ a ∈ L, diam (cell ε η a) < δ / 4)
    (hball : ∀ a ∈ L, (cell ε η a ∩ ball 0 ρ).Nonempty) (hX : innerNbhd (δ / 2) X ⊆ fillCells ε η L) :
    innerNbhd δ X ⊆
      fillCells ε η {a ∈ L | δ / 4 < infDist (vertexPoint ε η a) (frontier (fillCells ε η L))} := by
  intro x hx
  set U := fillCells ε η L with hU
  have hxU : x ∈ U := hX (innerNbhd_anti (by linarith) X hx)
  obtain ⟨a, haL, hxa⟩ : ∃ a ∈ L, x ∈ cell ε η a := by
    simpa only [hU, fillCells, mem_iUnion, exists_prop] using hxU
  -- every point outside `U` is at distance `≥ δ/2` from `x`
  have hC : ∀ z ∉ U, δ / 2 ≤ dist x z := by
    intro z hz
    by_contra hlt
    rw [not_le] at hlt
    apply hz
    apply hX
    have hzX : z ∈ X := by
      by_contra hzX
      have := le_dist_of_mem_innerNbhd hx hzX
      linarith
    refine ⟨hzX, le_infEDist.2 fun w hw => ?_⟩
    have h1 := le_dist_of_mem_innerNbhd hx hw
    have h2 := dist_triangle x z w
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- `U` is bounded, hence not the whole plane
  have hUR : U ⊆ ball 0 (ρ + δ / 4) := by
    intro y hy
    obtain ⟨b, hbL, hyb⟩ : ∃ b ∈ L, y ∈ cell ε η b := by
      simpa only [hU, fillCells, mem_iUnion, exists_prop] using hy
    obtain ⟨z, hzb, hz⟩ := hball b hbL
    rw [mem_ball] at hz ⊢
    have := dist_le_diam_of_mem (hb b hbL) hyb hzb
    have := dist_triangle y z 0
    linarith [hd b hbL]
  have hfr : (frontier U).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · rw [h] at hxU
      exact hxU
    · have hmem : ((ρ + δ / 4 : ℝ) : ℂ) ∈ U := h ▸ mem_univ _
      have := hUR hmem
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at this
      exact lt_irrefl _ (this.trans_le (le_abs_self _))
  -- `dist(x, ∂U) ≥ δ/2`
  have hfrU : frontier U ⊆ {z | δ / 2 ≤ dist x z} := by
    have h1 : frontier U ⊆ closure Uᶜ := by
      rw [← frontier_compl]
      exact frontier_subset_closure
    refine h1.trans (closure_minimal (fun z hz => hC z hz) ?_)
    exact isClosed_le continuous_const (continuous_const.dist continuous_id)
  have hxF : δ / 2 ≤ infDist x (frontier U) := by
    rw [infDist_eq_iInf]
    have : Nonempty (frontier U) := hfr.to_subtype
    exact le_ciInf fun y => hfrU y.2
  have h3 := infDist_le_infDist_add_dist (x := x) (y := vertexPoint ε η a) (s := frontier U)
  have h4 := dist_le_diam_of_mem (hb a haL) hxa (vertexPoint_mem_cell' hε η a)
  have h5 := hd a haL
  have hfin : δ / 4 < infDist (vertexPoint ε η a) (frontier U) := by linarith
  simp only [fillCells, mem_iUnion, exists_prop]
  exact ⟨a, ⟨haL, hfin⟩, hxa⟩

/-- Annealed union bound: if, off a set `B` of environments, the section of `E` is contained in that of `E₁`, then
`P*(E) ≤ P*(E₁) + P(B)` for the annealed outer probability with probability quenched laws. -/
theorem annealedOuterProb_le_add {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) [∀ ω, IsProbabilityMeasure (κ ω)] (E E₁ : Set (Ω × X)) (B : Set Ω)
    (h : ∀ ω, ω ∉ B → Prod.mk ω ⁻¹' E ⊆ Prod.mk ω ⁻¹' E₁) :
    annealedOuterProb P κ E ≤ annealedOuterProb P κ E₁ + P B := by
  unfold annealedOuterProb outerLIntegral
  set g₂ : Ω → ℝ≥0∞ := (toMeasurable P B).indicator 1 with hg₂
  have hg₂m : Measurable g₂ := measurable_one.indicator (measurableSet_toMeasurable P B)
  have hg₂i : ∫⁻ ω, g₂ ω ∂P = P B := by
    rw [hg₂, lintegral_indicator_one (measurableSet_toMeasurable P B), measure_toMeasurable]
  calc (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : (fun ω => κ ω (Prod.mk ω ⁻¹' E)) ≤ g), ∫⁻ ω, g ω ∂P)
      ≤ ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : (fun ω => κ ω (Prod.mk ω ⁻¹' E₁)) ≤ g),
          (∫⁻ ω, g ω ∂P + P B) := by
        refine le_iInf fun g => le_iInf fun hg => le_iInf fun hfg => ?_
        refine iInf_le_of_le (g + g₂) (iInf_le_of_le (hg.add hg₂m) (iInf_le_of_le ?_ ?_))
        · intro ω
          by_cases hω : ω ∈ B
          · have : g₂ ω = 1 := by
              rw [hg₂, indicator_of_mem (subset_toMeasurable P B hω), Pi.one_apply]
            simp only [Pi.add_apply, this]
            exact prob_le_one.trans le_add_self
          · exact (measure_mono (h ω hω)).trans ((hfg ω).trans le_self_add)
        · show ∫⁻ ω, g ω + g₂ ω ∂P ≤ _
          rw [lintegral_add_left hg, hg₂i]
    _ = (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : (fun ω => κ ω (Prod.mk ω ⁻¹' E₁)) ≤ g),
          ∫⁻ ω, g ω ∂P) + P B := by
        simp only [ENNReal.iInf_add]

end IDLALowerBound

end MatedCRT
