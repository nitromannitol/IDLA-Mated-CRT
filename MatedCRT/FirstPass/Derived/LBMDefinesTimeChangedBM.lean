import MatedCRT.FirstPass.Derived.MarkovTimeChange
import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.Proofs.LBM.TimeChangeContinuity
import LatticeProb.Prob.MarkovTimeScale

/-!
# The Liouville Brownian motion path laws define a time-changed Brownian motion

For a functional `F` of planar Brownian paths which is, almost surely under every start `z`, a time-change clock
(continuous, strictly increasing, `F b 0 = 0`, unbounded), the path laws `P_z` of the rescaled Liouville Brownian motion
`u ↦ b (F(b)⁻¹ (c u))`, `c > 0`, define a time-changed Brownian motion in the sense of Berestycki and Gwynne (2020),
Definition 7.2 (`DefinesTimeChangedBM`): the Brownian path `b` itself is the Brownian motion and
`τ_u = F(b)⁻¹ (c u)` is the continuous strictly increasing time change (Garban, Rhodes and Vargas,
*Liouville Brownian motion*, Ann. Probab. 44 (2016), Definition 2.17).

* `clockInverse_zero_of_isTimeChangeClock`: the inverse of a time-change clock vanishes at `0`.
* `definesTimeChangedBM_of_isTimeChangeClock`: Definition 7.2 for the law family of the rescaled Liouville
  Brownian motion.
-/

set_option autoImplicit false

open MeasureTheory MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The right-continuous inverse of a time-change clock vanishes at `0`. -/
theorem clockInverse_zero_of_isTimeChangeClock {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) :
    _root_.HarmonicBalls.clockInverse f 0 = 0 := by
  have h := MatedCRT.clockInverse_clockValue hf.map_zero hf.strictMono 0
  simpa [hf.map_zero] using h

/-- **The rescaled Liouville Brownian motion path laws define a time-changed Brownian motion**
(Berestycki–Gwynne (2020), Definition 7.2). Let `F` be, almost surely under planar Brownian motion from every
start `z`, a time-change clock, let `c ≠ 0`, and let `P_z` be the law under planar Brownian motion from `z` of the
rescaled Liouville Brownian path `u ↦ b (F(b)⁻¹ (c u))`. Then `P` defines a time-changed Brownian motion. -/
theorem definesTimeChangedBM_of_isTimeChangeClock {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {c : ℝ≥0} (hc : c ≠ 0)
    {P : PathLawFamily}
    (hF : ∀ z, ∀ᵐ b ∂(planarBrownianMotion z), IsTimeChangeClock (F b))
    (hg : ∀ z, AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z))
    (hP : ∀ z, (P z : Measure (ContinuousPath ℂ)) =
      (planarBrownianMotion z).map (fun b => LatticeProb.timeScalePath c (lbmContinuousPath F b))) :
    DefinesTimeChangedBM P := by
  intro z
  have hmeas : Measurable (LatticeProb.timeScalePath (E := ℂ) c) :=
    (LatticeProb.continuous_timeScalePath c).measurable
  refine ⟨ContinuousPath ℂ, inferInstance, planarBrownianMotion z, inferInstance, id,
    fun b => LatticeProb.timeScalePath c (lbmContinuousPath F b), fun b u => _root_.HarmonicBalls.clockInverse (F b) (c * u),
    measurable_id.aemeasurable, hmeas.comp_aemeasurable (hg z), ?_, ?_, hP z⟩
  · rw [Measure.map_id]
    rfl
  · filter_upwards [hF z] with b hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (IsTimeChangeClock.continuous_clockInverse hb).comp (continuous_const.mul continuous_id)
    · exact (IsTimeChangeClock.strictMono_clockInverse hb).comp
        (strictMono_mul_left_of_pos (pos_iff_ne_zero.2 hc))
    · simpa using clockInverse_zero_of_isTimeChangeClock hb
    · intro u
      simp only [LatticeProb.timeScalePath_apply, id]
      rw [lbmContinuousPath_of_isTimeChangeClock hb]
      rfl

end MatedCRT.FirstPass.Derived
