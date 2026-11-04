import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.IntermediateShell

/-! Contraction of the boundary maximum through the intermediate annulus. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- The origin cell is strictly inside the separating thickening of the
intermediate shell, so it avoids the frontier. -/
theorem intermediate_inner_contains_zero
    {ε s v : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 ≤ ε) (hs : 0 < s) (hv : 0 < v) (h0 : (0 : ℤ) ∈ Θ) :
    (0 : ℤ) ∈ cellVertices ε η (thickening (v / 2)
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))))) \
      cellVertices ε η (frontier (thickening (v / 2)
        (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ)))))) := by
  have hinside : cell ε η 0 ⊆ thickening (v / 2)
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ)))) := by
    intro z hz
    apply self_subset_thickening (by linarith : 0 < v / 2) _
    apply fillCells_subset_fill_intermediate hs
    exact mem_iUnion₂.mpr ⟨0, h0, hz⟩
  refine ⟨⟨vertexPoint ε η 0, vertexPoint_mem_cell hε η 0,
    hinside (vertexPoint_mem_cell hε η 0)⟩, ?_⟩
  rintro ⟨z, hzcell, hzfront⟩
  rw [isOpen_thickening.frontier_eq] at hzfront
  exact hzfront.2 (hinside hzcell)

/-- The separating inner cells lie in the next shell if its radius absorbs
the intermediate-shell radius, half the annulus radius and one diameter. -/
theorem intermediate_inner_subset_next_shell
    {ε s v D r : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hη : Continuous η)
    (hdiam : ∀ a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hradius : v / 2 + D + s ≤ r) :
    cellVertices ε η (thickening (v / 2)
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))))) \
      cellVertices ε η (frontier (thickening (v / 2)
        (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ)))))) ⊆
      cellVertices ε η (thickening r (fillCells ε η Θ)) := by
  intro a ha
  apply cellVertices_mono _ ha.1
  exact (thickening_fill_intermediate_subset hη Subset.rfl hdiam).trans
    (thickening_mono hradius _)

/-- The corrected annulus radius fits in the next shell if cells are at most
half the shell radius and the mass-bound constant is at most one. -/
theorem intermediate_radius_budget
    {r c D : ℝ} (hr : 0 ≤ r) (hc : c ≤ 1) (hD : D ≤ r / 2) :
    ((c / 8) * r) / 2 + D + r / 4 ≤ r := by
  have hcr : c * r ≤ r := by nlinarith
  linarith

/-- The survival estimate on the intermediate-shell frontier contracts the
next shell's boundary maximum. The set `A` contains precisely the occupied
vertices of the annulus. -/
theorem intermediate_annulus_boundary_contracts
    {m : ℤ → ℤ → ℕ} {ε ρ t q s v : ℝ} {η : ℝ → ℂ}
    {Θ I B Θnext : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hq : 0 ≤ q) (hs : 0 < s) (hv : 0 < v)
    (hη : Continuous η)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ)
    (hI : I = cellVertices ε η (thickening s (fillCells ε η Θ)))
    (hB : B = cellVertices ε η (thickening v (fillCells ε η I)) \ I)
    (hinner : (cellVertices ε η (thickening (v / 2) (fillCells ε η I)) \
      cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I)))).Finite)
    (hinner0 : (0 : ℤ) ∈ cellVertices ε η (thickening (v / 2) (fillCells ε η I)) \
      cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I))))
    (hnext : cellVertices ε η (thickening (v / 2) (fillCells ε η I)) \
      cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I))) ⊆ Θnext)
    (hodo : ∀ b ∈ B, stoppedOdometer m ε η ρ t b ≤
      (⨆ c : vBoundary m B, stoppedOdometer m ε η ρ t c) *
        (srwLaw m b {x | vExitTime B x <
          vHitTime (B \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : ∀ b ∈ cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I))),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x →
        x n ∈ B ∩ matedDiscreteCluster m ε η ρ t} ≤ ENNReal.ofReal q) :
    (⨆ b : vBoundary m Θnext, stoppedOdometer m ε η ρ t b) ≤
      (⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * q := by
  have hdisj : B ⊆ (vClosure m Θ)ᶜ := by
    rw [hB, hI]
    exact thickened_annulus_disjoint_graph_closure hε.le hs hadj
  apply next_shell_boundary_contracts_of_survival_bound hε ht hq hη isOpen_thickening
    hsymm hlf hsucc hadj hfin hlap hΘ h0 hdisj (Subset.rfl) hinner hinner0 hnext
  · intro b hb
    apply hodo b
    rw [hB]
    exact frontier_cells_subset_thickened_annulus (by linarith : 0 < v / 2)
      (by linarith : v / 2 < v) hb
  · exact hprob

end MatedCRT.Sec7
