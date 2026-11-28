import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Basic.Real.Basic

/-!
# Two path properties of the correlated Brownian pair

For real functions `X Y : ℝ → ℝ` of time:

* `NoOppositeSideMin X Y`: no time `t` is a minimum of `X` on a left neighbourhood `(t - h, t)` and of `Y` on a right
  neighbourhood `(t, t + h)`. For the two coordinates of a `γ`-correlated two-sided Brownian pair this is Shimura's
  theorem on meandering points (Shimura, *Meandering points of two-dimensional Brownian motion*, Kodai Math. J. 11
  (1988), Theorem 1), in both orders.
* `NowhereMonotone X`: `X` is neither monotone nor antitone on any interval of positive length.

Together with the fields of a Peanosphere curve they exclude continua of positive diameter among the triple points of
the curve.
-/

set_option autoImplicit false

open Set

namespace MatedCRT.PeanosphereTriplePoints

/-- No time is a minimum of `X` on a left neighbourhood and of `Y` on a right neighbourhood. -/
def NoOppositeSideMin (X Y : ℝ → ℝ) : Prop :=
  ∀ t h : ℝ, 0 < h → (∀ s ∈ Ioo (t - h) t, X t ≤ X s) → ¬ ∀ s ∈ Ioo t (t + h), Y t ≤ Y s

/-- `X` is neither monotone nor antitone on any interval of positive length. -/
def NowhereMonotone (X : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a < b → ¬ MonotoneOn X (Icc a b) ∧ ¬ AntitoneOn X (Icc a b)

end MatedCRT.PeanosphereTriplePoints
