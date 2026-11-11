import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# Deterministic chain from the cluster to the trace bound

The cluster is a set `F` of the plane which contains the cells of the vertices of `Θ`; `U1 = thickening (r/2) F` and
`U2 = thickening r F` are the two regions of `FrontierSeparation.trace_bound_of_frontier`. This file proves, with no
probability input beyond the exit-time finiteness `hexit` and the frontier bound `hfront`:

* `meetVerts_eq_of_isOpen`: for an open region the vertices of closed cells meeting it are the vertices of open cells
  meeting it (`cellVertices` of the printed proof, eq `V^ε(D)`);
* `closure_cell_subset_thickening_of_vClosure`: the closed cell of a vertex of the vertex closure `vClosure m Θ` lies in
  `thickening (r/2) F` when the cell diameter of that vertex is below `r/2` (Euclidean cell geometry, Armitage-Gardiner
  style closure of a connected cell meeting a neighbouring cell);
* `frontier_thickening_half_subset`: `frontier (thickening (r/2) F) ⊆ thickening r F`;
* `trace_bound_cluster`: the trace bound `s₂ ≤ P_a(hit `V(U₂) \ (S' ∪ Θ)` before exit of `V(U₂)`)` from the frontier
  bound at the frontier vertices.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

namespace Chain68

/-- For an open region `U`, the vertices whose closed cell meets `U` are the vertices whose open cell meets `U`. -/
theorem meetVerts_eq_of_isOpen {cell : ℤ → Set ℂ} {U : Set ℂ} (hU : IsOpen U) :
    FrontierSeparation.meetVerts cell U = {v | (cell v ∩ U).Nonempty} := by
  ext v
  simp only [FrontierSeparation.meetVerts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hxc, hxU⟩
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff.1 hxc U hU hxU
    exact ⟨y, hyc, hyU⟩
  · rintro ⟨y, hyc, hyU⟩
    exact ⟨y, subset_closure hyc, hyU⟩

/-- The frontier of the `r/2`-thickening of `F` lies in the `r`-thickening of `F` (`0 < r`). -/
theorem frontier_thickening_half_subset {F : Set ℂ} {r : ℝ} (hr : 0 < r) :
    frontier (Metric.thickening (r / 2) F) ⊆ Metric.thickening r F := by
  intro x hx
  have h1 : x ∈ closure (Metric.thickening (r / 2) F) := hx.1
  have h2 : x ∈ Metric.cthickening (r / 2) F := Metric.closure_thickening_subset_cthickening (r / 2) F h1
  exact Metric.cthickening_subset_thickening' hr (by linarith) F h2

/-- Two points of the closed cell of `a` are at distance at most the diameter of that cell. Let `p` lie in the closed
cells of `a` and of `b`; then the closed cell of `a` lies in the `r/2`-thickening of the cell of `b` when the cell of `a`
has diameter `d < r/2`. -/
theorem closure_cell_subset_thickening_of_near {cell : ℤ → Set ℂ} {a b : ℤ} {r d : ℝ} (hd : d < r / 2)
    (hbdd : Bornology.IsBounded (cell a)) (hdiam : Metric.diam (cell a) ≤ d)
    {p : ℂ} (hpa : p ∈ closure (cell a)) (hpb : p ∈ closure (cell b)) :
    closure (cell a) ⊆ Metric.thickening (r / 2) (cell b) := by
  intro x hx
  have hxp : dist x p ≤ d := by
    have h1 : dist x p ≤ Metric.diam (closure (cell a)) :=
      Metric.dist_le_diam_of_mem hbdd.closure hx hpa
    rw [Metric.diam_closure] at h1
    linarith
  obtain ⟨q, hq, hpq⟩ := Metric.mem_closure_iff.1 hpb ((r / 2 - d) / 2) (by linarith)
  refine Metric.mem_thickening_iff.2 ⟨q, hq, ?_⟩
  have htri : dist x q ≤ dist x p + dist p q := dist_triangle x p q
  linarith

/-- **Closed cell of a vertex of `vClosure m Θ`.** Let every cell of `Θ` lie in `F`, and let the cells of adjacent
vertices have intersecting closures (`hadj`). For `a ∈ vClosure m Θ` with cell diameter `d < r/2`, the closed cell of `a`
lies in `thickening (r/2) F`. -/
theorem closure_cell_subset_thickening_of_vClosure {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {F : Set ℂ} {Θ : Set ℤ}
    {r d : ℝ} (hr : 0 < r) (hd : d < r / 2) (hF : ∀ k ∈ Θ, cell k ⊆ F)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    {a : ℤ} (ha : a ∈ vClosure m Θ) (hbdd : Bornology.IsBounded (cell a))
    (hdiam : Metric.diam (cell a) ≤ d) :
    closure (cell a) ⊆ Metric.thickening (r / 2) F := by
  have hr2 : 0 < r / 2 := by linarith
  simp only [vClosure, vBoundary, Set.mem_union, Set.mem_ofPred_eq] at ha
  rcases ha with ha | ⟨_, b, hb, hmb⟩
  · exact (closure_mono (hF a ha)).trans (Metric.closure_subset_thickening hr2 F)
  · obtain ⟨p, hpb, hpa⟩ := hadj b a hmb
    intro x hx
    obtain ⟨z, hz, hxz⟩ :=
      Metric.mem_thickening_iff.1 (closure_cell_subset_thickening_of_near hd hbdd hdiam hpa hpb hx)
    exact Metric.mem_thickening_iff.2 ⟨z, hF b hb hz, hxz⟩

/-- **Trace bound of the cluster (deterministic chain).** Let `Θ` be a vertex set whose cells lie in `F`, let `a` be in
`vClosure m Θ` with cell diameter `d < r/2`, and let the exit of `V(thickening r F)` be almost surely finite. If every
frontier vertex `b ∈ V(∂U1)`, `U1 = thickening (r/2) F`, has walk-probability at most `1 - s₂` of staying in
`S' \ Θ` before exiting `V(U2) \ Θ`, then `s₂` is a lower bound for the probability that the walk from `a` visits
`V(U2) \ (S' ∪ Θ)` before exiting `V(U2)`. This is `FrontierSeparation.trace_bound_of_frontier` with the start and
frontier hypotheses supplied by the cluster geometry. -/
theorem trace_bound_cluster {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {F : Set ℂ} {Θ S' : Set ℤ} {a : ℤ} {r d : ℝ}
    (hr : 0 < r) (hd : d < r / 2)
    (hbdd : ∀ v, Bornology.IsBounded (cell v)) (hdiamA : Metric.diam (cell a) ≤ d)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    (hF : ∀ k ∈ Θ, cell k ⊆ F) (ha : a ∈ vClosure m Θ)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F)) x ≠ ⊤)
    {s2 : ℝ} (hs0 : 0 ≤ s2) (hs1 : s2 ≤ 1)
    (hfront : ∀ b ∈ FrontierSeparation.frontierVerts cell (Metric.thickening (r / 2) F),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) <
          vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ) x → x n ∈ S' \ Θ} ≤
        ENNReal.ofReal (1 - s2)) :
    ENNReal.ofReal s2 ≤ srwLaw m a
      (TraceFrom68.traceSet (FrontierSeparation.meetVerts cell (Metric.thickening r F))
        (FrontierSeparation.meetVerts cell (Metric.thickening r F) \ (S' ∪ Θ))) := by
  have hstart := closure_cell_subset_thickening_of_vClosure hr hd hF hadj ha (hbdd a) hdiamA
  exact FrontierSeparation.trace_bound_of_frontier Metric.isOpen_thickening
    (fun x hx => by
      obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx
      exact Metric.mem_thickening_iff.2 ⟨z, hz, by linarith⟩)
    (frontier_thickening_half_subset hr) hconn hne hadj hstart hexit Θ S' hs0 hs1 hfront

/-- **Trace bound of the cluster in `cellVertices` form.** As `trace_bound_cluster`, with the vertex sets written as
`{v | (cell v ∩ thickening r F).Nonempty}` (the vertex set `V^ε(D)` of `cellVertices` when `cell = cell ε η`). -/
theorem trace_bound_cluster_open {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {F : Set ℂ} {Θ S' : Set ℤ} {a : ℤ} {r d : ℝ}
    (hr : 0 < r) (hd : d < r / 2)
    (hbdd : ∀ v, Bornology.IsBounded (cell v)) (hdiamA : Metric.diam (cell a) ≤ d)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    (hF : ∀ k ∈ Θ, cell k ⊆ F) (ha : a ∈ vClosure m Θ)
    (hexit : ∀ᵐ x ∂srwLaw m a,
      vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F)) x ≠ ⊤)
    {s2 : ℝ} (hs0 : 0 ≤ s2) (hs1 : s2 ≤ 1)
    (hfront : ∀ b ∈ FrontierSeparation.frontierVerts cell (Metric.thickening (r / 2) F),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) <
          vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ) x → x n ∈ S' \ Θ} ≤
        ENNReal.ofReal (1 - s2)) :
    ENNReal.ofReal s2 ≤ srwLaw m a
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime {v | (cell v ∩ Metric.thickening r F).Nonempty} x ∧
        x n ∈ {v | (cell v ∩ Metric.thickening r F).Nonempty} \ (S' ∪ Θ)} := by
  have h := trace_bound_cluster hr hd hbdd hdiamA hconn hne hadj hF ha hexit hs0 hs1 hfront
  rw [meetVerts_eq_of_isOpen Metric.isOpen_thickening] at h
  exact h

end Chain68

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.Chain68.meetVerts_eq_of_isOpen
#print axioms MatedCRT.Chain68.frontier_thickening_half_subset
#print axioms MatedCRT.Chain68.closure_cell_subset_thickening_of_vClosure
#print axioms MatedCRT.Chain68.trace_bound_cluster
#print axioms MatedCRT.Chain68.trace_bound_cluster_open
