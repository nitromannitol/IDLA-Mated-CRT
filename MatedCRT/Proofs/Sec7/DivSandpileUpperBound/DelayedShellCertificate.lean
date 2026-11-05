import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DelayedShellConstruction
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Comparison

/-! Passing from a stopped boundary maximum to a shell certificate.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open Set Metric

/-- The ambient cell-size bound controls both the graph closures and the
finiteness of every shell up to a budgeted stopping index. -/
theorem iterated_shell_finite_and_diameter_of_total_budget
    {m : ℤ → ℤ → ℕ} {ε ρ D R₀ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hbudget : ((∑ j ∈ Finset.range n, r j) + ((n : ℝ) + 1) * (2 * D)) + R₀ < ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    (∀ k ≤ n, (Θ k).Finite) ∧
      (∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D) := by
  obtain ⟨hfill, hdiam⟩ := iterated_shell_geometry_of_total_budget Θ r n hε hη hD hR₀
    hr hadj h0 hstep hbudget hsize
  refine ⟨?_, hdiam⟩
  intro k hk
  apply hfin.subset
  intro a ha
  have hcell := vertexPoint_mem_own_cell hε η a
  refine ⟨vertexPoint ε η a, hcell, ball_subset_closedBall ?_⟩
  exact hfill k hk (mem_iUnion₂.mpr ⟨a, ha, hcell⟩)

/-- A threshold crossing for the boundary maximum, together with the shell
geometry up to that crossing, gives the finite shell certificate used in the
upper bound. -/
theorem delayed_shell_certificate_of_threshold
    {m : ℤ → ℤ → ℕ} {ε ρ t D B δ K α R : ℝ} {η : ℝ → ℂ} {Λ : Set ℂ}
    (Θ : ℕ → Set ℤ) (n : ℕ)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hD : 0 ≤ D) (hR : 0 < R)
    (hinit : Θ 0 = cellVertices ε η Λ) (hzero : (0 : ℤ) ∈ Θ 0)
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (delayedShellRadius (fun j =>
        ⨆ b : vBoundary m (Θ j), stoppedOdometer m ε η ρ t b) K α R k)
        (fillCells ε η (Θ k))))
    (hfinite : ∀ τ ≤ n,
      (∑ j ∈ Finset.range τ, delayedShellRadius (fun k =>
        ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) K α R j) +
          ((τ : ℝ) + 1) * (2 * D) ≤ δ → (Θ τ).Finite)
    (hdiam : ∀ τ ≤ n,
      (∑ j ∈ Finset.range τ, delayedShellRadius (fun k =>
        ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) K α R j) +
          ((τ : ℝ) + 1) * (2 * D) ≤ δ →
      ∀ k ≤ τ, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D)
    (hcross : ∃ τ ≤ n,
      (⨆ b : vBoundary m (Θ τ), stoppedOdometer m ε η ρ t b) ≤ B ∧
      (∑ j ∈ Finset.range τ, delayedShellRadius (fun k =>
        ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) K α R j) +
          ((τ : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ (T : ℕ → Set ℤ) (r : ℕ → ℝ) (τ : ℕ) (d : ℝ),
      0 ≤ d ∧ (∀ k < τ, 0 < r k) ∧ (0 : ℤ) ∈ T 0 ∧
      T 0 ⊆ cellVertices ε η Λ ∧
      (∀ k < τ, T (k + 1) = cellVertices ε η (thickening (r k) (fillCells ε η (T k)))) ∧
      (∀ k ≤ τ, ∀ a ∈ vClosure m (T k), diam (cell ε η a) ≤ d) ∧
      (∀ a ∈ vBoundary m (T τ), stoppedOdometer m ε η ρ t a ≤ B) ∧
      (∑ k ∈ Finset.range τ, r k) + ((τ : ℝ) + 1) * (2 * d) ≤ δ := by
  obtain ⟨τ, hτ, hmax, hbudget⟩ := hcross
  let O : ℕ → ℝ := fun k => ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b
  let r := delayedShellRadius O K α R
  refine ⟨Θ, r, τ, D, hD, ?_, hzero, ?_, ?_, ?_, ?_, hbudget⟩
  · intro k _
    exact delayedShellRadius_pos O K α R hR k
  · rw [hinit]
  · intro k hk
    exact hstep k (lt_of_lt_of_le hk hτ)
  · intro k hk
    exact hdiam τ hτ hbudget k hk
  · have := (vBoundary_finite hlf (hfinite τ hτ hbudget)).to_subtype
    have hbdd : BddAbove (range fun b : vBoundary m (Θ τ) =>
        stoppedOdometer m ε η ρ t b) := (Set.finite_range _).bddAbove
    intro a ha
    exact (le_ciSup hbdd ⟨a, ha⟩).trans hmax

/-- A budgeted threshold crossing and ambient cell bounds give a shell
certificate without requiring bounds beyond the stopping index. -/
theorem delayed_shell_certificate_of_ambient_bounds
    {m : ℤ → ℤ → ℕ} {ε ρ t D B δ K α R R₀ : ℝ} {η : ℝ → ℂ} {Λ : Set ℂ}
    (Θ : ℕ → Set ℤ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hR : 0 < R) (hR₀ : 0 ≤ R₀)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hinit : Θ 0 = cellVertices ε η Λ) (hzero : (0 : ℤ) ∈ Θ 0)
    (hΛ : Λ ⊆ closedBall 0 R₀) (hmargin : δ + R₀ < ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D)
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (delayedShellRadius (fun j =>
        ⨆ b : vBoundary m (Θ j), stoppedOdometer m ε η ρ t b) K α R k)
        (fillCells ε η (Θ k))))
    (hcross : ∃ τ ≤ n,
      (⨆ b : vBoundary m (Θ τ), stoppedOdometer m ε η ρ t b) ≤ B ∧
      (∑ j ∈ Finset.range τ, delayedShellRadius (fun k =>
        ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) K α R j) +
          ((τ : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ (T : ℕ → Set ℤ) (r : ℕ → ℝ) (τ : ℕ) (d : ℝ),
      0 ≤ d ∧ (∀ k < τ, 0 < r k) ∧ (0 : ℤ) ∈ T 0 ∧
      T 0 ⊆ cellVertices ε η Λ ∧
      (∀ k < τ, T (k + 1) = cellVertices ε η (thickening (r k) (fillCells ε η (T k)))) ∧
      (∀ k ≤ τ, ∀ a ∈ vClosure m (T k), diam (cell ε η a) ≤ d) ∧
      (∀ a ∈ vBoundary m (T τ), stoppedOdometer m ε η ρ t a ≤ B) ∧
      (∑ k ∈ Finset.range τ, r k) + ((τ : ℝ) + 1) * (2 * d) ≤ δ := by
  let O : ℕ → ℝ := fun k => ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b
  let r := delayedShellRadius O K α R
  have hgeom : ∀ τ ≤ n, (∑ j ∈ Finset.range τ, r j) +
      ((τ : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ k ≤ τ, (Θ k).Finite) ∧
        (∀ k ≤ τ, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D) := by
    intro τ hτ hb
    apply iterated_shell_finite_and_diameter_of_total_budget (ρ := ρ) Θ r τ hε hη hD hR₀
      (fun k _ => (delayedShellRadius_pos O K α R hR k).le) hadj
    · rw [hinit]
      exact cellVertices_mono hΛ
    · intro k hk
      exact hstep k (lt_of_lt_of_le hk hτ)
    · linarith
    · exact hfin
    · exact hsize
  apply delayed_shell_certificate_of_threshold Θ n hlf hD hR hinit hzero hstep
  · intro τ hτ hb
    exact (hgeom τ hτ hb).1 τ le_rfl
  · intro τ hτ hb
    exact (hgeom τ hτ hb).2
  · exact hcross

end MatedCRT.Sec7
