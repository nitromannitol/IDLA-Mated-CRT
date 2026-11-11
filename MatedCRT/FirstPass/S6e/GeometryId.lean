import MatedCRT.FirstPass.S6e.Geometry

/-!
# FIRST PASS: geometric identification of the countable cell formulas (LEMMA68 B2.1 (1)-(2), formula (9))

The countable formulas of `Geometry.lean` are identified with the geometric quantities of the write-up, for a
continuous curve `η : ℝ → ℂ` and `ε > 0`:
* `pointDist ε η Θ q = dist(η q, K)` with the filled set `K = ⋃_{w ∈ Θ} H_w = fillCells ε η Θ` (write-up (2));
* `cellDist ε η Θ k = inf_{u ∈ H_k} dist(u, K)` (write-up (3));
* `V(K + B_r) = {k : d_k < r}` (write-up (9)), where `K + B_r = Metric.thickening r K` (the open Minkowski sum).

Continuity of `η` is the hypothesis: `IsValid` gives it almost surely only (the a.s. wrapper is not part of this file).
The density step (`iInf_ratInt_eq`) uses only that `ratInt ε k` is dense in `I_k = [ε(k-1), εk]`, for `ε > 0`.
Terminology: filled set and cell distance as in Armstrong-Kuusi-Mourrat's cell decomposition of the mated-CRT map.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal Pointwise

namespace MatedCRT

namespace Lemma68GeometryId

open Lemma68Geometry

/-- Rational points of `I_k = [ε(k-1), εk]` are dense in `I_k` (write-up B2.1, `D_k = I_k ∩ ℚ`), for `ε > 0`. -/
lemma Icc_subset_closure_ratInt {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    Icc (ε * ((k : ℝ) - 1)) (ε * k) ⊆ closure (((↑) : ℚ → ℝ) '' ratInt ε k) := by
  have hlt : ε * ((k : ℝ) - 1) < ε * k := by rw [mul_sub, mul_one]; linarith
  rw [← closure_Ioo hlt.ne]
  apply closure_minimal _ isClosed_closure
  intro x hx
  have h1 : x ∈ closure (Ioo (ε * ((k : ℝ) - 1)) (ε * k) ∩ Set.range ((↑) : ℚ → ℝ)) :=
    (Rat.denseRange_cast : Dense (Set.range ((↑) : ℚ → ℝ))).open_subset_closure_inter isOpen_Ioo hx
  refine closure_mono ?_ h1
  rintro y ⟨hy, ⟨q, rfl⟩⟩
  exact ⟨q, ⟨hy.1.le, hy.2.le⟩, rfl⟩

/-- (B2.1, density) For a continuous `h : ℝ → ℝ≥0∞`, the infimum over the rational points of `I_k` equals the infimum
over `I_k`. This is the step that turns the countable formulas (3)-(4) into infima over the cell. -/
lemma iInf_ratInt_eq {h : ℝ → ℝ≥0∞} (hh : Continuous h) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    ⨅ q : ratInt ε k, h ((q : ℚ) : ℝ) = ⨅ s ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), h s := by
  apply le_antisymm
  · refine le_iInf₂ fun s hs => ?_
    have hmem : h s ∈ closure (h '' (((↑) : ℚ → ℝ) '' ratInt ε k)) :=
      mem_closure_image hh.continuousAt (Icc_subset_closure_ratInt hε k hs)
    have hle : closure (h '' (((↑) : ℚ → ℝ) '' ratInt ε k)) ⊆ Ici (⨅ q : ratInt ε k, h ((q : ℚ) : ℝ)) := by
      apply closure_minimal _ isClosed_Ici
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact iInf_le (fun q : ratInt ε k => h ((q : ℚ) : ℝ)) ⟨q, hq⟩
    exact hle hmem
  · refine le_iInf fun q => ?_
    exact iInf₂_le ((q : ℚ) : ℝ) q.2

/-- The filled set `K = ⋃_{w ∈ Θ} H_w` (write-up (2)) is the finite union of the cells over the index type `Θ`. -/
lemma infEDist_fillCells (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (x : ℂ) :
    Metric.infEDist x (fillCells ε η ↑Θ) =
      ⨅ w : Θ, ⨅ s ∈ Icc (ε * (((w : ℤ) : ℝ) - 1)) (ε * ((w : ℤ) : ℝ)), edist x (η s) := by
  have hU : fillCells ε η ↑Θ = ⋃ w : Θ, cell ε η (w : ℤ) := by
    ext y
    simp [fillCells, cell]
  rw [hU, Metric.infEDist_iUnion]
  refine iInf_congr fun w => ?_
  rw [cell, Metric.infEDist, iInf_image]

/-- (B2.1 (2), write-up (2)) `pointDist ε η Θ q` is the distance from `η q` to the filled set `K = fillCells ε η Θ`. -/
lemma pointDist_eq_infEDist {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (q : ℚ) :
    pointDist ε η Θ q = Metric.infEDist (η q) (fillCells ε η ↑Θ) := by
  rw [infEDist_fillCells]
  unfold pointDist
  refine iInf_congr fun w => ?_
  exact iInf_ratInt_eq (h := fun s => edist (η q) (η s)) (continuous_const.edist hη) hε (w : ℤ)

/-- (B2.1 (1), write-up (3)) The cell distance `d_k` is the infimum over the cell `H_k = η(I_k)` of the distance to `K`. -/
lemma cellDist_eq_iInf_cell {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (k : ℤ) :
    cellDist ε η Θ k = ⨅ u ∈ cell ε η k, Metric.infEDist u (fillCells ε η ↑Θ) := by
  have hcont : Continuous fun s : ℝ => Metric.infEDist (η s) (fillCells ε η ↑Θ) :=
    Metric.continuous_infEDist.comp hη
  unfold cellDist
  refine (iInf_congr fun q : ratInt ε k => pointDist_eq_infEDist hη hε Θ (q : ℚ)).trans
    ((iInf_ratInt_eq (h := fun s => Metric.infEDist (η s) (fillCells ε η ↑Θ)) hcont hε k).trans ?_)
  rw [cell, iInf_image]

/-- (B2.1 (1) and (9), write-up (9)) `V(K + B_r) = {k : d_k < r}`: the cells meeting the open Minkowski sum
`K + B_r = Metric.thickening r K` are exactly those with cell distance below `r`. -/
theorem cellVertices_thickening_eq {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ)
    (r : ℝ) :
    cellVertices ε η (thickening r (fillCells ε η ↑Θ)) = {k : ℤ | cellDist ε η Θ k < ENNReal.ofReal r} := by
  ext k
  simp only [cellVertices, Set.mem_ofPred_eq, Set.Nonempty, Set.mem_inter_iff,
    Metric.mem_thickening_iff_infEDist_lt]
  rw [cellDist_eq_iInf_cell hη hε Θ k]
  simp only [iInf_lt_iff, exists_prop]

/-- The open Minkowski sum `K + B_r` (with `B_r = ball 0 r` in `ℂ`) is the open thickening `Metric.thickening r K`. -/
lemma thickening_eq_add_ball (r : ℝ) (K : Set ℂ) : Metric.thickening r K = K + Metric.ball (0 : ℂ) r := by
  ext x
  rw [Metric.mem_thickening_iff, Set.mem_add]
  constructor
  · rintro ⟨z, hz, hd⟩
    refine ⟨z, hz, x - z, ?_, by abel⟩
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hd
  · rintro ⟨z, hz, y, hy, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hy

/-- (B2.1 (9), literal form) `V(K + B_r) = {k : d_k < r}` with `K + B_r = fillCells ε η Θ + ball 0 r`. -/
theorem cellVertices_add_ball_eq {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ)
    (r : ℝ) :
    cellVertices ε η (fillCells ε η ↑Θ + Metric.ball (0 : ℂ) r) =
      {k : ℤ | cellDist ε η Θ k < ENNReal.ofReal r} := by
  rw [← thickening_eq_add_ball]
  exact cellVertices_thickening_eq hη hε Θ r

/-- (B2.1, density, supremum form) For a continuous `h : ℝ → ℝ≥0∞`, the supremum over the rational points of `I_k`
equals the supremum over `I_k`; this turns the countable formula (4) into a supremum over the cell. -/
lemma iSup_ratInt_eq {h : ℝ → ℝ≥0∞} (hh : Continuous h) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    ⨆ q : ratInt ε k, h ((q : ℚ) : ℝ) = ⨆ s ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), h s := by
  apply le_antisymm
  · refine iSup_le fun q => ?_
    exact le_iSup₂ (f := fun s _ => h s) ((q : ℚ) : ℝ) q.2
  · refine iSup₂_le fun s hs => ?_
    have hmem : h s ∈ closure (h '' (((↑) : ℚ → ℝ) '' ratInt ε k)) :=
      mem_closure_image hh.continuousAt (Icc_subset_closure_ratInt hε k hs)
    have hle : closure (h '' (((↑) : ℚ → ℝ) '' ratInt ε k)) ⊆ Iic (⨆ q : ratInt ε k, h ((q : ℚ) : ℝ)) := by
      apply closure_minimal _ isClosed_Iic
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact le_iSup (fun q : ratInt ε k => h ((q : ℚ) : ℝ)) ⟨q, hq⟩
    exact hle hmem

/-- (B2.1 (1), write-up (4)) The maximal distance `M_k` is the supremum over the cell `H_k` of the distance to `K`. -/
lemma cellDistMax_eq_iSup_cell {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (k : ℤ) :
    cellDistMax ε η Θ k = ⨆ u ∈ cell ε η k, Metric.infEDist u (fillCells ε η ↑Θ) := by
  have hcont : Continuous fun s : ℝ => Metric.infEDist (η s) (fillCells ε η ↑Θ) :=
    Metric.continuous_infEDist.comp hη
  unfold cellDistMax
  refine (iSup_congr fun q : ratInt ε k => pointDist_eq_infEDist hη hε Θ (q : ℚ)).trans
    ((iSup_ratInt_eq (h := fun s => Metric.infEDist (η s) (fillCells ε η ↑Θ)) hcont hε k).trans ?_)
  rw [cell, iSup_image]

/-- Almost-sure form of the cell identification: the curve is continuous almost surely (write-up IsValid). -/
theorem ae_cellDist_eq_iInf_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ → ℂ}
    (hae : ∀ᵐ ω ∂P, Continuous (η ω)) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (k : ℤ) :
    ∀ᵐ ω ∂P, cellDist ε (η ω) Θ k = ⨅ u ∈ cell ε (η ω) k, Metric.infEDist u (fillCells ε (η ω) ↑Θ) :=
  hae.mono fun _ h => cellDist_eq_iInf_cell h hε Θ k

/-- Almost-sure form of `V(K + B_r) = {k : d_k < r}`. -/
theorem ae_cellVertices_add_ball_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ → ℂ}
    (hae : ∀ᵐ ω ∂P, Continuous (η ω)) {ε : ℝ} (hε : 0 < ε) (Θ : Finset ℤ) (r : ℝ) :
    ∀ᵐ ω ∂P, cellVertices ε (η ω) (fillCells ε (η ω) ↑Θ + Metric.ball (0 : ℂ) r) =
      {k : ℤ | cellDist ε (η ω) Θ k < ENNReal.ofReal r} :=
  hae.mono fun _ h => cellVertices_add_ball_eq h hε Θ r

/-- (B2.1 density step, general form) For a dense range `φ` and a continuous `F`, the infimum of `F ∘ φ` equals the
infimum of `F`. -/
lemma iInf_denseRange_eq {α β : Type*} [TopologicalSpace β] {φ : α → β} (hφ : DenseRange φ) {F : β → ℝ≥0∞}
    (hF : Continuous F) : ⨅ a, F (φ a) = ⨅ x, F x := by
  refine le_antisymm (le_iInf fun x => ?_) (le_iInf fun a => iInf_le F (φ a))
  have hmem : F x ∈ closure (F '' range φ) := mem_closure_image hF.continuousAt (hφ x)
  have hle : closure (F '' range φ) ⊆ Ici (⨅ a, F (φ a)) := by
    apply closure_minimal _ isClosed_Ici
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact iInf_le (fun a => F (φ a)) a
  exact hle hmem

/-- The rational pairs are dense in `ℂ` (B2.1 (5)): the map `(a, b) ↦ a + i b` from `ℚ × ℚ` has dense range. -/
lemma denseRange_ratPair : DenseRange (fun z : ℚ × ℚ => Complex.mk (z.1 : ℝ) (z.2 : ℝ)) := by
  have hg : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    DenseRange.prodMap Rat.denseRange_cast Rat.denseRange_cast
  have hs : Function.Surjective (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := fun w => ⟨(w.re, w.im), rfl⟩
  have hc : Continuous fun p : ℝ × ℝ => Complex.mk p.1 p.2 := Complex.equivRealProdCLM.symm.continuous
  exact DenseRange.comp hs.denseRange hg hc

/-- (B2.1 (5)) For a continuous `η`, the infimum over the rational parameters of the cell `I_k` of the distance from
`ζ` to `η q` is the distance from `ζ` to the cell `H_k = η(I_k)`. -/
lemma iInf_ratInt_edist_eq {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) (k : ℤ) :
    ⨅ q : ratInt ε k, edist ζ (η ((q : ℚ) : ℝ)) = Metric.infEDist ζ (cell ε η k) := by
  refine (iInf_ratInt_eq (h := fun s => edist ζ (η s)) (continuous_const.edist hη) hε k).trans ?_
  rw [cell, Metric.infEDist, iInf_image]

/-- (B2.1 (5), write-up (5)) The capacity radius `c_B` is the infimum over all centres `z ∈ ℂ` of the maximal distance
from `z` to the cells `H_v`, `v ∈ B`. -/
theorem capRadius_eq_iInf_complex {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (B : Finset ℤ) :
    capRadius ε η B = ⨅ z : ℂ, ⨆ v : B, Metric.infEDist z (cell ε η v.1) := by
  have hG : Continuous fun z : ℂ => ⨆ v : B, Metric.infEDist z (cell ε η v.1) := by
    simp only [← Finset.sup_univ_eq_iSup]
    exact Continuous.finset_sup_apply fun v _ => Metric.continuous_infEDist
  have h1 : capRadius ε η B =
      ⨅ z : ℚ × ℚ, ⨆ v : B, Metric.infEDist (Complex.mk (z.1 : ℝ) (z.2 : ℝ)) (cell ε η v.1) := by
    unfold capRadius
    refine iInf_congr fun z => iSup_congr fun v => ?_
    exact iInf_ratInt_edist_eq hη hε _ v.1
  exact h1.trans (iInf_denseRange_eq denseRange_ratPair hG)

end Lemma68GeometryId

end MatedCRT
