import MatedCRT.FirstPass.Derived.StopAtExitCmpContinuity
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.Proofs.LBM.OutwardCrossing
import MatedCRT.Proofs.LBM.BrownianExitBall

/-!
# Regular exit of planar Brownian motion from a disc

Planar Brownian motion started at a point `x` of the disc `ball z r` leaves the disc at a finite time almost surely,
and it exits regularly: immediately after its exit time it visits the complement of the closed disc at arbitrarily
small positive times (`MatedCRT.TruncatedLaws.RegularExit`; Mörters–Peres, *Brownian Motion*, Theorems 2.7 and
2.16). The regular exit follows from the outward radial excursion of the Brownian path at its exit time
(`MatedCRT.frozenBrownianOutwardExcursionAtExit_holds`, proved from Blumenthal's zero-one law and the strong Markov
property at the exit time): an increment with positive inner product against the outward normal `b(τ) - z` at a
point `b(τ)` of the circle leaves the closed disc.

Combined with the deterministic continuity of the stopping map (`MatedCRT.StopAtExitCmp`), this gives: for almost
every Brownian path `b` from `x`, the map `g ↦ stopAtExit (ball z r) g` is continuous at `b` for the distance
`cmpEDist` of curves modulo time parametrization. This is the probabilistic half of the passage from paths to paths
stopped at the exit of a disc in the uniform-start invariance principle (`MatedCRT.GMS21UniformStartInput`).

## Main statements

* `MatedCRT.StopAtExitCmp.regularExit_ball_of_outward_radial_excursion`: the deterministic reduction.
* `MatedCRT.StopAtExitCmp.ae_regularExit_ball_planarBrownian`: almost surely the exit time from `ball z r` is
  finite and the exit is regular.
* `MatedCRT.StopAtExitCmp.ae_cmpEDist_stopAtExit_ball_planarBrownian`: almost surely the stopping map is
  `cmpEDist`-continuous at the Brownian path.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

namespace MatedCRT.StopAtExitCmp

/-- A continuous path started in `ball z r`, with a finite exit time and an outward radial excursion at its exit
time, exits `ball z r` regularly. -/
theorem regularExit_ball_of_outward_radial_excursion {b : ContinuousPath ℂ} {z : ℂ} {r : ℝ}
    (h0 : b 0 ∈ ball z r) (hfin : ContinuousPath.exitTime (ball z r) b < ⊤)
    (hexc : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) b).toNNReal,
      0 < ⟪b (ContinuousPath.exitTime (ball z r) b).toNNReal - z,
        b t - b (ContinuousPath.exitTime (ball z r) b).toNNReal⟫_ℝ) :
    pathExitTime (ball z r) ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit (ball z r) ⇑b := by
  have hboundary : b (ContinuousPath.exitTime (ball z r) b).toNNReal ∈ sphere z r :=
    frontier_ball_subset_sphere (ContinuousPath.coordinate_exitTime_mem_frontier
      (ball z r) isOpen_ball b h0 (ne_of_lt hfin))
  have hreg : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) b).toNNReal,
      b t ∉ closure (ball z r) :=
    (frequently_outside_closedBall_of_outward_radial_excursion hboundary hexc).mono
      fun _ ht hmem => ht (closure_ball_subset_closedBall hmem)
  exact ⟨ne_of_lt hfin, Or.inr hreg⟩

/-- Planar Brownian motion started in `ball z r` almost surely leaves the disc at a finite time, and exits it
regularly. -/
theorem ae_regularExit_ball_planarBrownian {x z : ℂ} {r : ℝ} (hx : x ∈ ball z r) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      pathExitTime (ball z r) ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit (ball z r) ⇑b := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x, ae_planarBrownianMotion_exit_any_ball_lt_top x z r,
    frozenBrownianOutwardExcursionAtExit_holds x z r hx] with b h0 hfin hexc
  exact regularExit_ball_of_outward_radial_excursion (h0 ▸ hx) hfin hexc

/-- For almost every planar Brownian path `b` started in `ball z r`, stopping at the exit time of `ball z r` is
continuous at `b` for the distance `cmpEDist` of curves modulo time parametrization. -/
theorem ae_cmpEDist_stopAtExit_ball_planarBrownian {x z : ℂ} {r : ℝ} (hx : x ∈ ball z r) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ,
      cmpEDist g ⇑b < ENNReal.ofReal δ →
        cmpEDist (stopAtExit (ball z r) g) (stopAtExit (ball z r) ⇑b) < ENNReal.ofReal ε := by
  filter_upwards [ae_regularExit_ball_planarBrownian hx] with b hb ε hε
  exact cmpEDist_stopAtExit_lt_of_regularExit isOpen_ball b.continuous hb.1 hb.2 hε

end MatedCRT.StopAtExitCmp
