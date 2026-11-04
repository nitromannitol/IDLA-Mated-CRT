import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudePath
import MatedCRT.Draft.Section7

/-! Cell diameter estimates for the crude path in Proposition 7.1. -/

namespace MatedCRT.Sec7

open Set

/-- The endpoint representing a vertex belongs to its cell. -/
theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (a : ℤ) :
    vertexPoint ε η a ∈ cell ε η a := by
  refine ⟨ε * a, ⟨?_, le_rfl⟩, rfl⟩
  apply mul_le_mul_of_nonneg_left _ hε
  linarith

/-- If two cells meet and both have diameter at most `D`, their vertex points are
at distance at most `2D`. -/
theorem vertexPoint_dist_le_of_cells_meet {ε D : ℝ} {η : ℝ → ℂ} {a b : ℤ}
    (hε : 0 ≤ ε) (hmeet : (cell ε η a ∩ cell ε η b).Nonempty)
    (ha : ∀ x ∈ cell ε η a, ∀ y ∈ cell ε η a, dist x y ≤ D)
    (hb : ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ D) :
    dist (vertexPoint ε η a) (vertexPoint ε η b) ≤ 2 * D := by
  obtain ⟨z, hza, hzb⟩ := hmeet
  have h1 := ha _ (vertexPoint_mem_cell hε η a) z hza
  have h2 := hb z hzb _ (vertexPoint_mem_cell hε η b)
  linarith [dist_triangle (vertexPoint ε η a) z (vertexPoint ε η b)]

/-- A cell on an increasing odometer path lies near a vertex on the graph boundary.
This is the crude path estimate with the cell-diameter and adjacency hypotheses. -/
theorem increasing_path_cell_boundary_distance
    (m : ℤ → ℤ → ℕ) (Θ : Set ℤ) (p : List ℤ) (a b : ℤ)
    (ε D d M : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ)
    (hsymm : ∀ c e, m c e = m e c) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hd : 0 < d)
    (hu0 : 0 ≤ u a) (hout : a ∉ Θ) (hin : b ∈ Θ)
    (hhead : p.head? = some a) (hlast : p.getLast? = some b)
    (hedge : p.IsChain fun c e => m c e ≠ 0)
    (hinc : p.IsChain fun c e => u c + d ≤ u e)
    (hmeet : ∀ c ∈ p, ∀ e ∈ p, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ p, ∀ x ∈ cell ε η c, ∀ y ∈ cell ε η c, dist x y ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, u c ≤ M)
    (z : ℂ) (hz : z ∈ cell ε η a) :
    ∃ c ∈ vBoundary m Θ, c ∈ p ∧
      dist z (vertexPoint ε η c) ≤ D + M / d * (2 * D) := by
  have ha : a ∈ p := by
    cases p with
    | nil => simp at hhead
    | cons v q =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst v
      simp
  have hdist : ∀ c ∈ p, ∀ e ∈ p, m c e ≠ 0 →
      dist (vertexPoint ε η c) (vertexPoint ε η e) ≤ 2 * D := by
    intro c hc e he hce
    exact vertexPoint_dist_le_of_cells_meet hε (hmeet c hc e he hce) (hdiam c hc) (hdiam e he)
  obtain ⟨c, hcb, hcp, hdistc⟩ := increasing_list_path_boundary_distance m Θ p a b
    (vertexPoint ε η) u d M (2 * D) hsymm hd (by positivity) hu0 hout hin hhead hlast hedge hinc hdist hbound
  refine ⟨c, hcb, hcp, ?_⟩
  have hza := hdiam a ha z hz (vertexPoint ε η a) (vertexPoint_mem_cell hε η a)
  linarith [dist_triangle z (vertexPoint ε η a) (vertexPoint ε η c)]

/-- The support path hypothesis of Lemma 7.4 and a cell diameter bound place every
cell outside `Θ` near the graph boundary of `Θ`. -/
theorem crude_support_cell_boundary_distance
    (m : ℤ → ℤ → ℕ) (A Θ : Set ℤ) (ε D d M : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ)
    (hsymm : ∀ c e, m c e = m e c) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hd : 0 < d)
    (hη : Continuous η) (hzero : (0 : ℤ) ∈ Θ)
    (hnonneg : ∀ a ∈ A, 0 ≤ u a)
    (hpaths : ∀ a ∈ A \ {0}, ∃ p : List ℤ, IsVPathIn m A p a 0 ∧
      p.IsChain fun c e => u c + d ≤ u e)
    (hmeet : ∀ c e, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ A, Metric.diam (cell ε η c) ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, u c ≤ M)
    (a : ℤ) (ha : a ∈ A) (hout : a ∉ Θ) (z : ℂ) (hz : z ∈ cell ε η a) :
    ∃ c ∈ vBoundary m Θ, dist z (vertexPoint ε η c) ≤ D + M / d * (2 * D) := by
  have hane : a ≠ 0 := fun h => hout (h ▸ hzero)
  obtain ⟨p, ⟨hhead, hlast, hpA, hedge⟩, hinc⟩ := hpaths a ⟨ha, hane⟩
  have hdiam' : ∀ c ∈ p, ∀ x ∈ cell ε η c, ∀ y ∈ cell ε η c, dist x y ≤ D := by
    intro c hc x hx y hy
    have hb : Bornology.IsBounded (cell ε η c) := (isCompact_Icc.image hη).isBounded
    exact (Metric.dist_le_diam_of_mem hb hx hy).trans (hdiam c (hpA c hc))
  obtain ⟨c, hc, _, hdist⟩ := increasing_path_cell_boundary_distance m Θ p a 0
    ε D d M η u hsymm hε hD hd (hnonneg a ha) hout hzero hhead hlast hedge hinc
    (fun c _ e _ hce => hmeet c e hce) hdiam' hbound z hz
  exact ⟨c, hc, hdist⟩

/-- The filled support is contained in a controlled closed neighborhood of the
filled graph closure of `Θ`. This is the deterministic conclusion of the crude-path step. -/
theorem fill_support_subset_cthickening
    (m : ℤ → ℤ → ℕ) (A Θ : Set ℤ) (ε D d M : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ)
    (hsymm : ∀ c e, m c e = m e c) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hd : 0 < d) (hM : 0 ≤ M)
    (hη : Continuous η) (hzero : (0 : ℤ) ∈ Θ)
    (hnonneg : ∀ a ∈ A, 0 ≤ u a)
    (hpaths : ∀ a ∈ A \ {0}, ∃ p : List ℤ, IsVPathIn m A p a 0 ∧
      p.IsChain fun c e => u c + d ≤ u e)
    (hmeet : ∀ c e, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ A, Metric.diam (cell ε η c) ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, u c ≤ M) :
    fillCells ε η A ⊆ Metric.cthickening (D + M / d * (2 * D)) (fillCells ε η (vClosure m Θ)) := by
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  by_cases hΘ : a ∈ Θ
  · apply Metric.mem_cthickening_of_dist_le z z _ _
    · exact mem_iUnion₂.mpr ⟨a, Or.inl hΘ, hza⟩
    · simp only [dist_self]
      positivity
  · obtain ⟨c, hc, hdist⟩ := crude_support_cell_boundary_distance m A Θ ε D d M η u
      hsymm hε hD hd hη hzero hnonneg hpaths hmeet hdiam hbound a ha hΘ z hza
    apply Metric.mem_cthickening_of_dist_le z (vertexPoint ε η c) _ _
    · exact mem_iUnion₂.mpr ⟨c, Or.inr hc, vertexPoint_mem_cell hε η c⟩
    · exact hdist

/-- Filling the graph closure adds at most one cell diameter. -/
theorem fill_closure_subset_cthickening (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (ε D : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hmeet : ∀ c e, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ vClosure m A, Metric.diam (cell ε η c) ≤ D) :
    fillCells ε η (vClosure m A) ⊆ Metric.cthickening D (fillCells ε η A) := by
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  rcases ha with ha | ⟨hnot, b, hb, hab⟩
  · exact Metric.self_subset_cthickening _ (mem_iUnion₂.mpr ⟨a, ha, hza⟩)
  · obtain ⟨w, hwb, hwa⟩ := hmeet b a hab
    have hbdd : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
    have hdist : dist z w ≤ D :=
      (Metric.dist_le_diam_of_mem hbdd hza hwa).trans (hdiam a (Or.inr ⟨hnot, b, hb, hab⟩))
    exact Metric.mem_cthickening_of_dist_le z w D _ (mem_iUnion₂.mpr ⟨b, hb, hwb⟩) hdist

/-- Crude paths control the filled closure of the support, with one extra cell
diameter for its graph boundary. -/
theorem fill_support_closure_subset_cthickening
    (m : ℤ → ℤ → ℕ) (A Θ : Set ℤ) (ε D d M : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ)
    (hsymm : ∀ c e, m c e = m e c) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hd : 0 < d) (hM : 0 ≤ M)
    (hη : Continuous η) (hzero : (0 : ℤ) ∈ Θ)
    (hnonneg : ∀ a ∈ A, 0 ≤ u a)
    (hpaths : ∀ a ∈ A \ {0}, ∃ p : List ℤ, IsVPathIn m A p a 0 ∧
      p.IsChain fun c e => u c + d ≤ u e)
    (hmeet : ∀ c e, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ vClosure m A, Metric.diam (cell ε η c) ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, u c ≤ M) :
    fillCells ε η (vClosure m A) ⊆
      Metric.cthickening (D + (D + M / d * (2 * D))) (fillCells ε η (vClosure m Θ)) := by
  have hsupport := fill_support_subset_cthickening m A Θ ε D d M η u hsymm hε hD hd hM
    hη hzero hnonneg hpaths hmeet (fun c hc => hdiam c (Or.inl hc)) hbound
  have hR : 0 ≤ D + M / d * (2 * D) := by positivity
  exact (fill_closure_subset_cthickening m A ε D η hη hmeet hdiam).trans
    ((Metric.cthickening_subset_of_subset D hsupport).trans
      (Metric.cthickening_cthickening_subset hD hR _))

/-- Pointwise application of the event in `CrudeUpperBoundStmt`: once the boundary
odometer and cell diameters are controlled, the stopped cluster has the claimed crude
spatial bound. -/
theorem crudeUpperBound_event_confinement
    (m : ℤ → ℤ → ℕ) (Θ : Set ℤ) (ε ρ t D M : ℝ) (η : ℝ → ℂ)
    (hsymm : ∀ c e, m c e = m e c) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hd : 0 < (Real.log ε⁻¹)⁻¹ ^ 2) (hη : Continuous η) (hzero : (0 : ℤ) ∈ Θ)
    (hpaths : ∀ a ∈ matedDiscreteCluster m ε η ρ t \ {0}, ∃ p : List ℤ,
      IsVPathIn m (matedDiscreteCluster m ε η ρ t) p a 0 ∧
        p.IsChain fun c e => stoppedOdometer m ε η ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤
          stoppedOdometer m ε η ρ t e)
    (hmeet : ∀ c e, m c e ≠ 0 → (cell ε η c ∩ cell ε η e).Nonempty)
    (hdiam : ∀ c ∈ vClosure m (matedDiscreteCluster m ε η ρ t), Metric.diam (cell ε η c) ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ M) :
    fillCells ε η (vClosure m (matedDiscreteCluster m ε η ρ t)) ⊆
      Metric.cthickening (D + (D + M / ((Real.log ε⁻¹)⁻¹ ^ 2) * (2 * D)))
        (fillCells ε η (vClosure m Θ)) := by
  apply fill_support_closure_subset_cthickening m (matedDiscreteCluster m ε η ρ t) Θ
    ε D ((Real.log ε⁻¹)⁻¹ ^ 2) M η (stoppedOdometer m ε η ρ t)
    hsymm hε hD hd hM hη hzero ?_ hpaths hmeet hdiam hbound
  intro a ha
  have haW : a ∈ cellVertices ε η (Metric.closedBall 0 ρ) := by
    obtain ⟨z, hzc, hzball⟩ := ha.1
    exact ⟨z, hzc, Metric.ball_subset_closedBall hzball⟩
  simp only [stoppedOdometer, haW, ↓reduceIte]
  exact le_of_lt (sub_pos.mpr ha.2)

end MatedCRT.Sec7
