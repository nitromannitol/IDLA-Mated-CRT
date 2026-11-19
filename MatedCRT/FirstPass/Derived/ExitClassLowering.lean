import MatedCRT.FirstPass.Derived.ExitReparamAssembly

/-!
# Lowering the exit radius for stopped curve class laws

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Lemma 7.4, deterministic reduction of the radii.

If a law `P` on continuous planar paths carries no interval of constancy and the stopped curve class at exit from
the ball of radius `r'` has the law it has under planar Brownian motion from `z` (`‖z‖ < r'`), then the stopped
curve class at exit from every smaller ball `B(0, r)`, `r ≤ r'`, has the Brownian law too: both measures are carried
by paths without interval of constancy that start in `B(0, r')` and leave it, and on such paths the class at
radius `r'` determines the class at radius `r` (`ExitReparamAssembly.stoppedExitCurve_ball_eq_of_le`).

* `map_stoppedExitCurve_eq_of_le`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric HarmonicBalls MarkovProcess LatticeProb
open scoped ENNReal NNReal

namespace MatedCRT.ExitClassLowering

open MatedCRT.ExitReparamAssembly MatedCRT.ExitReparamSetup

/-- **Lowering the exit radius for the stopped curve class law** (BG20, Lemma 7.4).  If `P` has almost surely no
interval of constancy and the class stopped at exit from `B(0, r')` has the law it has under planar Brownian motion
from `z ∈ B(0, r')`, then so does the class stopped at exit from `B(0, r)` for every `r ≤ r'`. -/
theorem map_stoppedExitCurve_eq_of_le {z : ℂ} {r r' : ℝ} (hrr : r ≤ r') (hz : ‖z‖ < r')
    {P : Measure (ContinuousPath ℂ)}
    (hflat : P {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    (hb : P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r')) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r'))) :
    P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) := by
  have hgP := ae_levelGood_of_map_eq (r := fun _ : ℕ => r') hz monotone_const hflat (fun _ => hb)
  have hgW := ae_levelGood_of_map_eq (r := fun _ : ℕ => r') hz monotone_const
    (planarBrownianMotion_noFlat z) (fun _ => rfl)
  refine map_eq_map_of_eqOn_fibers
    (p := MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r'))
    (N := {f | LevelGood (fun _ : ℕ => r') f})
    (MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball)
    (MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball) ?_
    (ae_iff.1 hgP) (ae_iff.1 hgW) hb
  rintro a ⟨ha1, ha2, ha3⟩ a' ⟨hb1, hb2, hb3⟩ hcls
  exact stoppedExitCurve_ball_eq_of_le hrr ha1 hb1 ha2 hb2 (ha3 0) (hb3 0) hcls

end MatedCRT.ExitClassLowering
