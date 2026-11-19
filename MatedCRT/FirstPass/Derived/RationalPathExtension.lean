import MatedCRT.FirstPass.Derived.AdaptedVersionOfLimitInProbability
import MatedCRT.FirstPass.Derived.RevuzOptionalClockInverse

/-!
# Continuous planar paths are measurably determined by their values at rational times

The restriction `x ↦ (q ↦ x_q)` of a continuous planar path to the rational times is a continuous injective map
from the space of continuous paths (a standard Borel space) to `ℚ → ℂ`, hence a measurable embedding
(Lusin–Souslin).  Consequently the continuous extension `ratExtend` of a function on the rationals, taken to be
a fixed default path when there is none, is Borel measurable, and recovers every continuous path from its
rational values.  A path-valued map is therefore measurable as soon as each of its values at rational times is
(`measurable_ratExtend_comp`).
-/

namespace MatedCRT

open MeasureTheory MarkovProcess
open scoped NNReal

/-- The restriction of a continuous planar path to the rational times (negative rationals read at time `0`). -/
noncomputable def ratRestrict (x : ContinuousPath ℂ) : ℚ → ℂ :=
  fun q => x (AdaptedVersion.ratTime q)

theorem continuous_ratRestrict : Continuous ratRestrict :=
  continuous_pi fun q => continuous_eval_const (AdaptedVersion.ratTime q)

theorem injective_ratRestrict : Function.Injective ratRestrict := by
  intro x y h
  refine ContinuousMap.ext fun t => ?_
  have hxy : (x : ℝ≥0 → ℂ) = y := by
    refine AdaptedVersion.denseRange_ratTime.equalizer x.continuous y.continuous ?_
    funext q
    exact congrFun h q
  exact congrFun hxy t

theorem measurableEmbedding_ratRestrict : MeasurableEmbedding ratRestrict :=
  continuous_ratRestrict.measurable.measurableEmbedding injective_ratRestrict

/-- The continuous path with prescribed values on the rational times, when it exists; the zero path
otherwise. -/
noncomputable def ratExtend : (ℚ → ℂ) → ContinuousPath ℂ :=
  Function.extend ratRestrict id fun _ => (ContinuousMap.const ℝ≥0 0 : ContinuousPath ℂ)

theorem ratExtend_ratRestrict (x : ContinuousPath ℂ) : ratExtend (ratRestrict x) = x :=
  injective_ratRestrict.extend_apply _ _ x

theorem measurable_ratExtend : Measurable ratExtend :=
  measurableEmbedding_ratRestrict.measurable_extend measurable_id measurable_const

/-- A path-valued map is measurable once each of its values at a rational time is. -/
theorem measurable_ratExtend_comp {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℚ → ℂ}
    (hf : ∀ q, Measurable fun ω => f ω q) : Measurable fun ω => ratExtend (f ω) :=
  measurable_ratExtend.comp (measurable_pi_iff.2 hf)

/-- If the rational values of `f ω` are those of a continuous path `x`, then the extension is `x`. -/
theorem ratExtend_eq_of_forall {f : ℚ → ℂ} {x : ContinuousPath ℂ}
    (h : ∀ q, f q = x (AdaptedVersion.ratTime q)) : ratExtend f = x := by
  have : f = ratRestrict x := funext h
  rw [this, ratExtend_ratRestrict]

end MatedCRT
