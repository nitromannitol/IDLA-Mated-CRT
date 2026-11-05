import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellSequence

/-! Construction of shell sequences with a one-step-delayed radius.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

/-- The current and preceding shells in a delayed shell iteration. -/
noncomputable def delayedShellState {A : Type} (initial : A)
    (step : A → ℝ → A) (maximum : A → ℝ) (K α R : ℝ) : ℕ → A × A
  | 0 => (initial, initial)
  | n + 1 =>
      let state := delayedShellState initial step maximum K α R n
      (step state.1 (max ((maximum state.2 * K) ^ α) R), state.1)

/-- The second component of the state is the preceding shell, with the
initial shell used at time zero. -/
theorem delayedShellState_previous {A : Type} (initial : A)
    (step : A → ℝ → A) (maximum : A → ℝ) (K α R : ℝ) (n : ℕ) :
    (delayedShellState initial step maximum K α R n).2 =
      (delayedShellState initial step maximum K α R n.pred).1 := by
  cases n <;> rfl

/-- Any shell update and boundary-maximum function admit a sequence using
exactly the delayed radii of the dyadic bootstrap. -/
theorem exists_delayed_shell_sequence {A : Type} (initial : A)
    (step : A → ℝ → A) (maximum : A → ℝ) (K α R : ℝ) :
    ∃ Θ : ℕ → A, Θ 0 = initial ∧
      ∀ n, Θ (n + 1) = step (Θ n)
        (delayedShellRadius (fun k => maximum (Θ k)) K α R n) := by
  let Θ : ℕ → A := fun n => (delayedShellState initial step maximum K α R n).1
  refine ⟨Θ, rfl, ?_⟩
  intro n
  change step (Θ n) (max ((maximum (delayedShellState initial step maximum K α R n).2 * K) ^ α) R) = _
  rw [delayedShellState_previous]
  rfl

/-- The mated-CRT shells can be constructed with the initial harmonic-ball
cells and the one-step-delayed stopped-odometer radius. -/
theorem exists_delayed_mated_shell_sequence
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) (Λ : Set ℂ)
    (K α R : ℝ) :
    ∃ Θ : ℕ → Set ℤ, Θ 0 = cellVertices ε η Λ ∧
      ∀ n, Θ (n + 1) = cellVertices ε η
        (Metric.thickening (delayedShellRadius (fun k =>
          ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) K α R n)
          (fillCells ε η (Θ n))) := by
  exact exists_delayed_shell_sequence (cellVertices ε η Λ)
    (fun U r => cellVertices ε η (Metric.thickening r (fillCells ε η U)))
    (fun U => ⨆ b : vBoundary m U, stoppedOdometer m ε η ρ t b) K α R

end MatedCRT.Sec7
