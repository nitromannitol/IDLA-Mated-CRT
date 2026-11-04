import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable

/-! Measurable projections of compact families with strict constraints. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric

/-- A closed relation with a strictly positive continuous constraint has a
measurable projection when the quantified space is compact. -/
theorem measurableSet_exists_mem_closed_pos
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    (F : Set (X × Y)) (hF : IsClosed F) (g : X × Y → ℝ) (hg : Continuous g) :
    MeasurableSet {x | ∃ y, (x, y) ∈ F ∧ 0 < g (x, y)} := by
  let A : ℕ → Set (X × Y) := fun n => F ∩ {p | 1 / ((n : ℝ) + 1) ≤ g p}
  have hA : ∀ n, IsClosed (A n) := fun n =>
    hF.inter (isClosed_le continuous_const hg)
  have heq : {x | ∃ y, (x, y) ∈ F ∧ 0 < g (x, y)} =
      ⋃ n, Prod.fst '' A n := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, Prod.exists]
    constructor
    · rintro ⟨y, hy, hpos⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, x, y, ⟨hy, hn.le⟩, rfl⟩
    · rintro ⟨n, x', y, ⟨hy, hbound⟩, rfl⟩
      exact ⟨y, hy, (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans_le hbound⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => (isClosedMap_fst_of_compactSpace _ (hA n)).measurableSet

/-- The distance from a point to a time-indexed curve cell, written as a
compact infimum so that it varies continuously with the curve and point. -/
noncomputable def curveCellDistance (ε : ℝ) (k : ℤ) (p : C(ℝ, ℂ) × ℂ) : ℝ :=
  sInf ((fun t => dist p.2 (p.1 t)) '' Icc (ε * (k - 1)) (ε * k))

theorem continuous_curveCellDistance (ε : ℝ) (k : ℤ) :
    Continuous (curveCellDistance ε k) := by
  unfold curveCellDistance
  apply isCompact_Icc.continuous_sInf
  exact (continuous_snd.comp continuous_fst).dist
    (ContinuousEval.continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

theorem curveCellDistance_eq_infDist (ε : ℝ) (k : ℤ)
    (hI : (Icc (ε * (k - 1)) (ε * k)).Nonempty) (p : C(ℝ, ℂ) × ℂ) :
    curveCellDistance ε k p = infDist p.2 (cell ε p.1 k) := by
  have hcell : (cell ε p.1 k).Nonempty := hI.image p.1
  have h := (Metric.isGLB_infDist (x := p.2) hcell).csInf_eq
    (hcell.image (fun y => dist p.2 y))
  simpa [curveCellDistance, cell, image_image, Function.comp_def] using h

/-- For a nonempty time interval, positive distance is exactly exclusion
from the corresponding cell. -/
theorem curveCellDistance_pos_iff (ε : ℝ) (k : ℤ)
    (hI : (Icc (ε * (k - 1)) (ε * k)).Nonempty) (p : C(ℝ, ℂ) × ℂ) :
    0 < curveCellDistance ε k p ↔ p.2 ∉ cell ε p.1 k := by
  rw [curveCellDistance_eq_infDist ε k hI p]
  have hc : IsClosed (cell ε p.1 k) :=
    (isCompact_Icc.image p.1.continuous).isClosed
  exact (hc.notMem_iff_infDist_pos (hI.image p.1)).symm

end MatedCRT
