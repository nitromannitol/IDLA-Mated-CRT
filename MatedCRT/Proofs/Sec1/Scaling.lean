import MatedCRT.Draft.Section1
import LatticeProb.Analysis.MetricRescaling

/-!
# Deterministic scaling covariance for the proof of Theorems 1.4 and 1.6 (lines 3284-3336)

For `b > 0`, `R > 0`, the rescaled environment of Section 8.1 has curve `η^b = R⁻¹ η(b ·)` and boundary-length pair
`(L^b, R^b) = b^{-1/2} (L, R)(b ·)`. This file proves the deterministic facts used to transfer Proposition 8.1 from the
rescaled environment at cell size `ε / b` to the original one at cell size `ε`:

* `bmEdgeCount_rescale`: the mated-CRT map (Definition 1.1) of `c (L, R)(b ·)` with cell size `ε / b` is the map of
  `(L, R)` with cell size `ε` (any `c > 0`);
* `mem_cell_rescale`, `fillCells_rescale`: the cells of `R⁻¹ η(b ·)` with cell size `ε / b` are `R⁻¹` times the cells
  of `η` with cell size `ε`;
* `infEDist_mul_le`: `dist(R x, s) ≤ R dist(x, R⁻¹ s)`;
* `approximatesWithin_of_rescaled`: if `B⁻_{δ'}(R⁻¹ Λ) ⊆ R⁻¹ X ⊆ B⁺_{δ'}(R⁻¹ Λ)` and `R δ' ≤ δ` then
  `B⁻_δ(Λ) ⊆ X ⊆ B⁺_δ(Λ)`;
* `tendsto_measure_lt_atTop`: an a.e.-measurable real random variable is tight, `P[R > M] → 0` as `M → ∞`.
-/

namespace MatedCRT

namespace Sec1

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-! ## The mated-CRT map of the time-rescaled boundary-length pair -/

/-- The image of `[p, q]` under `s ↦ c X(b s)` is `c` times the image of `[b p, b q]` under `X`. -/
theorem image_Icc_rescale {b c : ℝ} (hb : 0 < b) (X X' : ℝ → ℝ) (hX : ∀ s, X' s = c * X (b * s)) (p q : ℝ) :
    X' '' Icc p q = (fun y => c * y) '' (X '' Icc (b * p) (b * q)) :=
  LatticeProb.MetricRescaling.image_Icc_rescale hb X X' hX p q

/-- `inf (c A) = c inf A` for `c ≥ 0`. -/
theorem sInf_image_mul {c : ℝ} (hc : 0 ≤ c) (A : Set ℝ) : sInf ((fun y => c * y) '' A) = c * sInf A := by
  have h := Real.sInf_smul_of_nonneg hc A
  simp only [smul_eq_mul] at h
  rw [← h, ← Set.image_smul]
  rfl

/-- The adjacency condition (eq:edge-map) of `c X(b ·)` with cell size `ε / b` is that of `X` with cell size `ε`. -/
theorem bmAdjacent_rescale {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c) (X X' : ℝ → ℝ) (hX : ∀ s, X' s = c * X (b * s))
    (j k : ℤ) : bmAdjacent (ε / b) X' j k ↔ bmAdjacent ε X j k := by
  have e1 : ∀ x : ℝ, b * (ε / b * x - ε / b) = ε * x - ε := fun x => by field_simp
  have e2 : ∀ x : ℝ, b * (ε / b * x) = ε * x := fun x => by field_simp
  unfold bmAdjacent
  rw [image_Icc_rescale hb X X' hX, image_Icc_rescale hb X X' hX, image_Icc_rescale hb X X' hX]
  simp only [e1, e2]
  rw [sInf_image_mul hc.le, sInf_image_mul hc.le, sInf_image_mul hc.le, ← mul_max_of_nonneg _ _ hc.le]
  exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩

/-- **The map of the rescaled boundary-length pair** (Definition 1.1): the mated-CRT map of `c (L, R)(b ·)` with cell
size `ε / b` is the map of `(L, R)` with cell size `ε`. -/
theorem bmEdgeCount_rescale {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c) (L R L' R' : ℝ → ℝ)
    (hL : ∀ s, L' s = c * L (b * s)) (hR : ∀ s, R' s = c * R (b * s)) (j k : ℤ) :
    bmEdgeCount (ε / b) L' R' j k = bmEdgeCount ε L R j k := by
  have hL' : bmAdjacent (ε / b) L' = bmAdjacent ε L :=
    funext fun j => funext fun k => propext (bmAdjacent_rescale hb hc L L' hL j k)
  have hR' : bmAdjacent (ε / b) R' = bmAdjacent ε R :=
    funext fun j => funext fun k => propext (bmAdjacent_rescale hb hc R R' hR j k)
  unfold bmEdgeCount
  rw [hL', hR']

/-! ## Cells of the rescaled curve -/

/-- A point `x` lies in the cell of `k` for the curve `R⁻¹ η(b ·)` with cell size `ε / b` iff `R x` lies in the cell of
`k` for `η` with cell size `ε`. -/
theorem mem_cell_rescale {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (k : ℤ) (x : ℂ) : x ∈ cell (ε / b) η' k ↔ R * x ∈ cell ε η k := by
  have e1 : b * (ε / b * ((k : ℝ) - 1)) = ε * ((k : ℝ) - 1) := by field_simp
  have e2 : b * (ε / b * (k : ℝ)) = ε * k := by field_simp
  simp only [cell, mem_image, mem_Icc]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    refine ⟨b * s, ⟨?_, ?_⟩, ?_⟩
    · rw [← e1]; exact mul_le_mul_of_nonneg_left h1 hb.le
    · rw [← e2]; exact mul_le_mul_of_nonneg_left h2 hb.le
    · rw [hη, mul_inv_cancel_left₀ hR]
  · rintro ⟨u, ⟨h1, h2⟩, hu⟩
    refine ⟨u / b, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hb, mul_comm, e1]; exact h1
    · rw [div_le_iff₀ hb, mul_comm, e2]; exact h2
    · rw [hη, mul_div_cancel₀ u hb.ne', hu, inv_mul_cancel_left₀ hR]

/-- The union of the cells of `A` for `R⁻¹ η(b ·)` with cell size `ε / b` is `R⁻¹` times that for `η` with cell size
`ε`. -/
theorem fillCells_rescale {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (A : Set ℤ) :
    fillCells (ε / b) η' A = {x | R * x ∈ fillCells ε η A} := by
  ext x
  simp only [fillCells, mem_iUnion, exists_prop, mem_ofPred_eq, mem_cell_rescale hb hR η η' hη]

/-! ## Neighbourhoods under dilation -/

/-- `edist (R x) (R w) = R edist x w` for real `R > 0`. -/
theorem edist_ofReal_mul {R : ℝ} (hR : 0 < R) (x w : ℂ) :
    edist ((R : ℂ) * x) ((R : ℂ) * w) = ENNReal.ofReal R * edist x w :=
  LatticeProb.MetricRescaling.edist_ofReal_mul hR x w

/-- Lower bound for the distance to a dilated set: if `R⁻¹ s ⊆ t` then `R dist(x, t) ≤ dist(R x, s)`. -/
theorem ofReal_mul_infEDist_le {R : ℝ} (hR : 0 < R) (x : ℂ) {s t : Set ℂ}
    (hst : ∀ y ∈ s, (R : ℂ)⁻¹ * y ∈ t) :
    ENNReal.ofReal R * infEDist x t ≤ infEDist ((R : ℂ) * x) s :=
  LatticeProb.MetricRescaling.ofReal_mul_infEDist_le hR x hst

/-- Cancellation of a positive real factor in `ℝ≥0∞`. -/
theorem le_of_ofReal_mul_le {R : ℝ} (hR : 0 < R) {a c : ℝ≥0∞}
    (h : ENNReal.ofReal R * a ≤ ENNReal.ofReal R * c) : a ≤ c :=
  LatticeProb.MetricRescaling.le_of_ofReal_mul_le hR h

/-- `dist(R x, s) ≤ R dist(x, R⁻¹ s)` for real `R > 0`, with `R⁻¹ s = {z : R z ∈ s}`. -/
theorem infEDist_mul_le {R : ℝ} (hR : 0 < R) (x : ℂ) (s : Set ℂ) :
    infEDist ((R : ℂ) * x) s ≤ ENNReal.ofReal R * infEDist x {z | (R : ℂ) * z ∈ s} :=
  LatticeProb.MetricRescaling.infEDist_mul_le hR x s

/-- **Rescaling the approximation event**: if `B⁻_{δ'}(R⁻¹ Λ) ⊆ R⁻¹ X ⊆ B⁺_{δ'}(R⁻¹ Λ)` and `R δ' ≤ δ` (with `R > 0`),
then `B⁻_δ(Λ) ⊆ X ⊆ B⁺_δ(Λ)`. Here `R⁻¹ Y = {z : R z ∈ Y}`. -/
theorem approximatesWithin_of_rescaled {R δ δ' : ℝ} (hR : 0 < R) (hRδ : R * δ' ≤ δ)
    {Λ X : Set ℂ} (h : ApproximatesWithin δ' {z | (R : ℂ) * z ∈ Λ} {z | (R : ℂ) * z ∈ X}) :
    ApproximatesWithin δ Λ X := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRδ' : ENNReal.ofReal R * ENNReal.ofReal δ' ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul hR.le]; exact ENNReal.ofReal_le_ofReal hRδ
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · -- inner bound: `x = R⁻¹ y ∈ B⁻_{δ'}(R⁻¹ Λ)`
    have hx : (R : ℂ)⁻¹ * y ∈ innerNbhd δ' {z | (R : ℂ) * z ∈ Λ} := by
      refine ⟨by simpa [mul_inv_cancel_left₀ hR'] using hy.1, ?_⟩
      have h1 := infEDist_mul_le hR ((R : ℂ)⁻¹ * y) Λᶜ
      rw [mul_inv_cancel_left₀ hR'] at h1
      refine le_of_ofReal_mul_le hR ?_
      calc ENNReal.ofReal R * ENNReal.ofReal δ' ≤ ENNReal.ofReal δ := hRδ'
        _ ≤ infEDist y Λᶜ := hy.2
        _ ≤ ENNReal.ofReal R * infEDist ((R : ℂ)⁻¹ * y) {z | (R : ℂ) * z ∈ Λᶜ} := h1
        _ = ENNReal.ofReal R * infEDist ((R : ℂ)⁻¹ * y) {z | (R : ℂ) * z ∈ Λ}ᶜ := rfl
    have := h.1 hx
    simpa [mul_inv_cancel_left₀ hR'] using this
  · -- outer bound: `x = R⁻¹ y ∈ R⁻¹ X ⊆ B⁺_{δ'}(R⁻¹ Λ)`
    have hx : (R : ℂ)⁻¹ * y ∈ {z | (R : ℂ) * z ∈ X} := by simpa [mul_inv_cancel_left₀ hR'] using hy
    have h2 : infEDist ((R : ℂ)⁻¹ * y) {z | (R : ℂ) * z ∈ Λ} ≤ ENNReal.ofReal δ' := h.2 hx
    have h1 := infEDist_mul_le hR ((R : ℂ)⁻¹ * y) Λ
    rw [mul_inv_cancel_left₀ hR'] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 zero_le).trans hRδ')

/-- `B⁻_δ(Λ) ⊆ X ⊆ B⁺_δ(Λ)` is monotone in `δ`. -/
theorem ApproximatesWithin.mono {δ δ' : ℝ} (hδ : δ' ≤ δ) {Λ X : Set ℂ} (h : ApproximatesWithin δ' Λ X) :
    ApproximatesWithin δ Λ X :=
  ⟨fun _ hy => h.1 ⟨hy.1, (ENNReal.ofReal_le_ofReal hδ).trans hy.2⟩,
    fun _ hy => (h.2 hy).trans (ENNReal.ofReal_le_ofReal hδ)⟩

/-! ## Tightness of a real random variable -/

/-- An a.e.-measurable real random variable under a finite measure is tight: `P[R > M] → 0` as `M → ∞`. -/
theorem tendsto_measure_lt_atTop {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {R : Ω → ℝ} (hR : AEMeasurable R P) : Tendsto (fun M : ℝ => P {ω | M < R ω}) atTop (𝓝 0) :=
  LatticeProb.MetricRescaling.tendsto_measure_lt_atTop hR

end Sec1

end MatedCRT
