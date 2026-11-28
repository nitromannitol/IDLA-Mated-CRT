import MatedCRT.FirstPass.Derived.ZeroConeLemmaA4Proof

/-!
# The tilted area measure and the offsets of the two quantum clocks

The proof of the phase periods of the polygonal observables (`ZeroConePolygonalPhasePeriods`, the step of
Gwynne–Miller–Sheffield, arXiv:1705.11161v5, proof of Proposition 3.1, p. 23, lines 1193-1196) compares the quantum
clocks of one Lebesgue-parametrized curve `e` for an area measure `μ` and for the tilted measure `e^g μ`, `g` a smooth
bump. This file defines

* `tiltArea g μ`: the measure `μ` with density `e^g`;
* `clockOffset g μ e b`: the offsets `d_+ = ∫_{e[0,∞)} (e^g - 1) dμ` (`b = true`) and `d_- = -∫_{e(-∞,0]} (e^g - 1) dμ`
  (`b = false`) by which the tilted clock differs from the old one on the future and past time tails;
* `timeHalf e b`: the future half `e[0,∞)` (`b = true`) and the past half `e(-∞,0]` (`b = false`) of the curve.
-/

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace MatedCRT.ZeroConePolygonal

/-- The area measure `μ` tilted by `e^g`: the measure with density `z ↦ e^{g(z)}` with respect to `μ`. -/
def tiltArea (g : ℂ → ℝ) (μ : Measure ℂ) : Measure ℂ :=
  μ.withDensity fun z => ENNReal.ofReal (Real.exp (g z))

/-- The offsets of the tilted quantum clock of the curve `e` on its two time tails:
`d_+ = ∫_{e[0,∞)} (e^g - 1) dμ` for `b = true` and `d_- = -∫_{e(-∞,0]} (e^g - 1) dμ` for `b = false`. -/
def clockOffset (g : ℂ → ℝ) (μ : Measure ℂ) (e : C(ℝ, ℂ)) : Bool → ℝ
  | true => ∫ z in e '' Ici 0, (Real.exp (g z) - 1) ∂μ
  | false => -∫ z in e '' Iic 0, (Real.exp (g z) - 1) ∂μ

/-- The time halves of a curve: the future half `e[0,∞)` for `b = true` and the past half `e(-∞,0]` for `b = false`. -/
def timeHalf (e : C(ℝ, ℂ)) : Bool → Set ℂ
  | true => e '' Ici 0
  | false => e '' Iic 0

end MatedCRT.ZeroConePolygonal
