import MatedCRT.FirstPass.Derived.AreaCellCoveredShiftedSelectors
import LatticeProb.Bonanno.BouRabeeGwynne.SelectedExcursionOscillation

/-! # Brownian skeleton excursions of the selected-ball scheme have small oscillation

The transfer on shifted area-cell networks carries the oscillation of the Brownian
skeleton excursions as an hypothesis.  When the covering balls have a common radius
`ρ`, this hypothesis holds for every starting selection: each excursion is stopped at
the exit of a ball of radius `ρ` that contains its starting point, so its oscillation is
at most `2 ρ`. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal
universe u

/-- Almost surely every Brownian skeleton excursion of the selected-ball scheme with
common radius `ρ` has oscillation at most `2 ρ`, for the selectors induced by the cell
selection `cellSelector (E i) (choice i)` whose selected balls contain the margin
neighbourhood of their argument. -/
theorem ae_brownianSkeletonExcursion_curveOscillationLe_selectedBalls
    {J : Type u} [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ]
    (hμ : LatticeProb.IsStandardBrownianLaw μ)
    (center : J → LatticeProb.Euc 2) (rad : J → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hrad : ∀ j, rad j = ρ) {margin : ℝ} (hmargin : 0 < margin)
    (select : ℕ → LatticeProb.Euc 2 → Option J) (hs : ∀ n, Measurable (select n))
    (hsel : ∀ n x j, select n x = some j → ball x (margin / 2) ⊆ ball (center j) (rad j))
    (z : LatticeProb.Euc 2) (initial : J) (hz : select 0 z = some initial) :
    ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion (fun j => ball (center j) (rad j)) z initial
        (brownianSelectorForWalk select) i ω).2 ∈ curveOscillationLe (2 * ρ) := by
  have hrad' : rad = fun _ => ρ := funext hrad
  subst hrad'
  have hmem : ∀ n x j, select n x = some j → x ∈ ball (center j) ρ := fun n x j h =>
    hsel n x j h (mem_ball_self (by positivity))
  exact standardBrownianLaw_skeleton_ae_oscillation (by norm_num) hμ center hρ select hs hmem
    initial z (hmem 0 z initial hz)

end MatedCRT
