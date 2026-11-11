import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExcursionInterpolation

/-! # Geometry of the edge entering a boundary cell -/

namespace MatedCRT

open Set Metric
open scoped NNReal

/-- Representatives of intersecting cells are separated by at most the sum
of their diameters. -/
theorem dist_vertexPoint_le_of_intersecting_cells
    {ε d₁ d₂ : ℝ} {η : ℝ → ℂ} {a b : ℤ} (hε : 0 ≤ ε)
    (hη : Continuous η) (ha : diam (cell ε η a) ≤ d₁)
    (hb : diam (cell ε η b) ≤ d₂)
    (hinter : (cell ε η a ∩ cell ε η b).Nonempty) :
    dist (vertexPoint ε η a) (vertexPoint ε η b) ≤ d₁ + d₂ := by
  obtain ⟨q, hqa, hqb⟩ := hinter
  have h₁ := (dist_le_diam_of_mem (Sec7.cell_isBounded hη a)
    (Sec7.vertexPoint_mem_cell hε a) hqa).trans ha
  have h₂ := (dist_le_diam_of_mem (Sec7.cell_isBounded hη b)
    hqb (Sec7.vertexPoint_mem_cell hε b)).trans hb
  exact (dist_triangle _ q _).trans (add_le_add h₁ h₂)

/-- During one edge, the interpolated walk stays in any closed disk
containing both endpoints. -/
theorem interpolatedWalk_mem_closedBall_on_edge
    {ε mε : ℝ} (hm : 0 < mε) {η : ℝ → ℂ} {x : ℕ → ℤ}
    {z : ℂ} {R : ℝ} (k : ℕ)
    (hleft : vertexPoint ε η (x k) ∈ closedBall z R)
    (hright : vertexPoint ε η (x (k + 1)) ∈ closedBall z R)
    {t : ℝ≥0} (hlo : (k : ℝ) ≤ mε * (t : ℝ))
    (hhi : mε * (t : ℝ) ≤ (k + 1 : ℕ)) :
    interpolatedWalk ε η mε x t ∈ closedBall z R := by
  have h0 : 0 ≤ mε * (t : ℝ) := mul_nonneg hm.le t.2
  rcases eq_or_lt_of_le hhi with heq | hlt
  · have ht : t = ((((k + 1 : ℕ) : ℝ) / mε).toNNReal) := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)]
      apply (eq_div_iff hm.ne').2
      linarith
    rw [ht, interpolatedWalk_natCast_div hm]
    exact hright
  · have hfloor : ⌊mε * (t : ℝ)⌋₊ = k := by
      apply (Nat.floor_eq_iff h0).2
      constructor
      · exact hlo
      · simpa only [Nat.cast_add, Nat.cast_one] using hlt
    have hθ : 0 ≤ mε * (t : ℝ) - (k : ℝ) := sub_nonneg.mpr hlo
    have hθ' : 0 ≤ 1 - (mε * (t : ℝ) - (k : ℝ)) := by
      push_cast at hlt
      linarith
    have hc := convex_closedBall z R hleft hright hθ' hθ (by ring)
    simpa only [interpolatedWalk, hfloor, Complex.real_smul] using hc

/-- If two successive cells meet and each has diameter at most `d`, every
point on their interpolated edge is at distance at most `2 * d` from the
representative of the second cell. -/
theorem dist_interpolatedWalk_le_two_diam_on_edge
    {ε mε d : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (hη : Continuous η) (x : ℕ → ℤ) (k : ℕ)
    (ha : diam (cell ε η (x k)) ≤ d)
    (hb : diam (cell ε η (x (k + 1))) ≤ d)
    (hinter : (cell ε η (x k) ∩ cell ε η (x (k + 1))).Nonempty)
    {t : ℝ≥0} (hlo : (k : ℝ) ≤ mε * (t : ℝ))
    (hhi : mε * (t : ℝ) ≤ (k + 1 : ℕ)) :
    dist (interpolatedWalk ε η mε x t) (vertexPoint ε η (x (k + 1))) ≤ 2 * d := by
  have hd : 0 ≤ d := diam_nonneg.trans ha
  apply mem_closedBall.mp
  apply interpolatedWalk_mem_closedBall_on_edge hm k ?_ ?_ hlo hhi
  · apply mem_closedBall.mpr
    have h := dist_vertexPoint_le_of_intersecting_cells hε hη ha hb hinter
    linarith
  · exact mem_closedBall_self (by linarith)

end MatedCRT

#print axioms MatedCRT.dist_vertexPoint_le_of_intersecting_cells
#print axioms MatedCRT.interpolatedWalk_mem_closedBall_on_edge
#print axioms MatedCRT.dist_interpolatedWalk_le_two_diam_on_edge
