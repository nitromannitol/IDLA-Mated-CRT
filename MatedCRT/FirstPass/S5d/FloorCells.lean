import MatedCRT.FirstPass.S5c.HExclusive
import MatedCRT.Defs.Notation

/-!
# Proposition 5.1, floor argument: exclusive representatives in the inner neighbourhood

Written source: corrected tex 2362-2363 (`[C21]`: the floor `u^ε(a) ≥ c ε⁻¹` on the targets `a ∈ V^ε(B⁻_δ(Λ_t))`) and the two deterministic facts formalized here:
* every cell of positive mass has a point lying in no other cell (`S5c.exists_exclusive_mem_cell`, S5c/HExclusive.lean:66, from
  the quantum-area parametrization `IsAreaParametrized`, Defs/Setting.lean:125);
* once the cells have diameter below `δ/4`, every cell meeting `B⁻_{δ/2}(Λ_t)` lies in `B⁻_{δ/4}(Λ_t)`.

Not here: the strict gap of [C20], the rescaled convergence of Theorem `convergence-divisible` and `m_ε ≍ ε⁻¹`. They are the open
input `StoppedFloorStep` (S5d/StoppedExitInput.lean:129), whose convergence part is not formalized.
Inner neighbourhoods are `innerNbhd δ X = B⁻_δ(X)` (Defs/Notation.lean:30).
-/

open MeasureTheory Set Metric

namespace MatedCRT

/-- `B⁻_δ(X) ⊆ B⁻_{δ/2}(X)`: the inner neighbourhoods decrease in the width. -/
lemma innerNbhd_half_of_innerNbhd {δ : ℝ} (hδ : 0 < δ) (X : Set ℂ) :
    innerNbhd δ X ⊆ innerNbhd (δ / 2) X :=
  fun y hy => ⟨hy.1, (ENNReal.ofReal_le_ofReal (by linarith)).trans hy.2⟩

/-- Points of `B⁻_{δ/2}(X)` at distance below `δ/4` lie in `B⁻_{δ/4}(X)`: `dist(z, Xᶜ) ≥ dist(y, Xᶜ) - dist(y, z)` and `z ∈ X`
(the inner-neighbourhood step of the referee, lines 153-175). -/
lemma mem_innerNbhd_quarter_of_dist_lt {δ : ℝ} (hδ : 0 < δ) {X : Set ℂ} {y z : ℂ}
    (hy : y ∈ innerNbhd (δ / 2) X) (hyz : dist y z < δ / 4) : z ∈ innerNbhd (δ / 4) X := by
  have hsum : ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) = ENNReal.ofReal (δ / 2) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hlt : edist y z < ENNReal.ofReal (δ / 4) := by
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hyz
  have hdist : ENNReal.ofReal (δ / 4) ≤ Metric.infEDist z Xᶜ := by
    by_contra hc
    have hc' := not_le.1 hc
    have h1 : ENNReal.ofReal (δ / 2) ≤ edist y z + Metric.infEDist z Xᶜ :=
      hy.2.trans Metric.infEDist_le_edist_add_infEDist
    have h2 : edist y z + Metric.infEDist z Xᶜ < ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) :=
      ENNReal.add_lt_add hlt hc'
    rw [hsum] at h2
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  refine ⟨?_, hdist⟩
  by_contra hzX
  have h0 : Metric.infEDist z Xᶜ = 0 := Metric.infEDist_zero_of_mem (mem_compl hzX)
  rw [h0] at hdist
  exact absurd hdist (not_le.2 (ENNReal.ofReal_pos.2 (by linarith)))

/-- A set `C` of diameter below `δ/4` that meets `B⁻_{δ/2}(X)` lies in `B⁻_{δ/4}(X)` (the referee's "once the maximum cell
diameter is less than `δ/4`, every cell meeting `B⁻_{δ/2}(Λ_t)` lies in `B⁻_{δ/4}(Λ_t)`"). -/
lemma subset_innerNbhd_quarter_of_small {δ : ℝ} (hδ : 0 < δ) {X C : Set ℂ}
    (hsmall : ∀ x ∈ C, ∀ y ∈ C, dist x y < δ / 4) (hmeet : ∃ y ∈ C, y ∈ innerNbhd (δ / 2) X) :
    C ⊆ innerNbhd (δ / 4) X := by
  obtain ⟨y, hyC, hy⟩ := hmeet
  intro z hz
  exact mem_innerNbhd_quarter_of_dist_lt hδ hy (hsmall y hyC z hz)

/-- **Exclusive floor representatives (referee lines 153-175; corrected tex 2362, [C21]).** Let `η` be an area parametrization of
`μ` and `ε > 0`. Suppose every cell `cell ε η k` has diameter below `δ/4` (`hsmall`; supplied by the cell-size estimate
Lemma 2.8 on the relevant event, not used here). For a target `a ∈ V^ε(B⁻_δ(X))` (`cellVertices ε η (innerNbhd δ X)`) there is a point `x`
of the cell `a` that lies in no other cell, and this `x` lies in `B⁻_{δ/4}(X)`. The representative `x` is chosen in a deterministic
proof; no measurable selection is needed. -/
theorem exists_exclusive_point_innerNbhd_quarter {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) {X : Set ℂ}
    (hsmall : ∀ k : ℤ, ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y < δ / 4)
    {a : ℤ} (ha : a ∈ cellVertices ε η (innerNbhd δ X)) :
    ∃ x ∈ cell ε η a, (∀ b : ℤ, x ∈ cell ε η b → b = a) ∧ x ∈ innerNbhd (δ / 4) X := by
  obtain ⟨x, hxa, hex⟩ := S5c.exists_exclusive_mem_cell hap hε a
  refine ⟨x, hxa, hex, ?_⟩
  obtain ⟨y, hyc, hyB⟩ := ha
  exact subset_innerNbhd_quarter_of_small hδ (hsmall a) ⟨y, hyc, innerNbhd_half_of_innerNbhd hδ X hyB⟩ hxa

end MatedCRT
