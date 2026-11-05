import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DelayedShellConstruction
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialPoleLocalization

/-! Delayed shell sequences based at the harmonic-ball cells.
The mated-CRT infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open Set Metric

/-- Choose the delayed mated-CRT shell sequence at every mesh and environment. -/
noncomputable def initialDelayedShells {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t K α q ε : ℝ) (ω : Ω) :
    ℕ → Set ℤ :=
  Classical.choose (exists_delayed_mated_shell_sequence
    (S.mult ε ω) ε (S.η ω) ρ t (Λ ω t) (ε * K) α (ε ^ q))

/-- The chosen shells start with all cells meeting the harmonic ball and
follow the delayed-odometer recursion. -/
theorem initialDelayedShells_spec {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t K α q ε : ℝ) (ω : Ω) :
    let Θ := initialDelayedShells S Λ ρ t K α q ε ω
    Θ 0 = cellVertices ε (S.η ω) (Λ ω t) ∧
      ∀ k, Θ (k + 1) = cellVertices ε (S.η ω)
        (thickening (delayedShellRadius (fun j =>
          ⨆ b : vBoundary (S.mult ε ω) (Θ j), stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b)
          (ε * K) α (ε ^ q) k) (fillCells ε (S.η ω) (Θ k))) :=
  Classical.choose_spec (exists_delayed_mated_shell_sequence
    (S.mult ε ω) ε (S.η ω) ρ t (Λ ω t) (ε * K) α (ε ^ q))

/-- If the source lies in the harmonic ball, its vertex lies in the initial
shell; any localized source ball is covered by the cells of that shell. -/
theorem initialDelayedShells_source {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t K α q ε : ℝ) (ω : Ω)
    (hε : 0 < ε) (hη0 : S.η ω 0 = 0) (hsurj : Function.Surjective (S.η ω))
    (hzero : (0 : ℂ) ∈ Λ ω t) {s : ℝ} (hball : ball (0 : ℂ) s ⊆ Λ ω t) :
    (0 : ℤ) ∈ initialDelayedShells S Λ ρ t K α q ε ω 0 ∧
      ball (0 : ℂ) s ⊆ fillCells ε (S.η ω) (initialDelayedShells S Λ ρ t K α q ε ω 0) := by
  rw [(initialDelayedShells_spec S Λ ρ t K α q ε ω).1]
  constructor
  · refine ⟨0, ?_, hzero⟩
    simpa [vertexPoint, hη0] using (vertexPoint_mem_cell (η := S.η ω) hε.le 0)
  · exact hball.trans (subset_fillCells_cellVertices_of_surjective hε hsurj _)

end MatedCRT.Sec7
