import MatedCRT.FirstPass.Derived.LQGMeasureChart
import MatedCRT.FirstPass.Derived.LQGMeasureChartConePoint
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.Main

/-!
# The coordinate change of the LQG measure for all inverse charts

`lqgMeasureChartStmt_of_envelope`: `LQGMeasureChartStmt γ` for every `0 < γ < 2` from the one cited input
`SheffieldWangEnvelope`, the regularity input being proved (`GFFLocalRegularity.zeroBoundaryGFFLocalRegularity`).

`lqgMeasureChartStmt_of_inputs`: `LQGMeasureChartStmt γ` for every `0 < γ < 2` (the coordinate change of the LQG measure
for all inverse charts at once, step R3 of the Revuz route in `ChartFieldLBM.lean`), from the two cited inputs
`SheffieldWangEnvelope` (Sheffield–Wang (2016), arXiv:1605.06171v2, Theorem 1.1 and the envelope statement at the end
of the proof of Theorem 1.2) and `ZeroBoundaryGFFLocalRegularity` (the local negative regularity of the zero-boundary
GFF on a disc, De Nitti–Schweiger, arXiv:2301.13781v4, Proposition 2.1).

The proof: in every valid environment the field has the coordinate change on every open set
(`MatedCRTEnv.IsValid.ae_openChartProp`: the disc statement `sheffieldWangDiscConformal_of_inputs`, the Markov
decomposition on discs, the cone decomposition `cone = G − γ log |·| + v` and the rooted measure of the whole-plane
GFF at the cone point), and the inverse charts are the case `V = U` (`lqgMeasureChartStmt_of_openChartProp`, with the
Borel map `chartMeasure γ`).
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- **The coordinate change of the LQG measure for all inverse charts** (`LQGMeasureChartStmt γ`, `0 < γ < 2`), from the
cited inputs `SheffieldWangEnvelope` and `ZeroBoundaryGFFLocalRegularity`. -/
theorem lqgMeasureChartStmt_of_inputs (hE : SheffieldWangEnvelope) (hR : ZeroBoundaryGFFLocalRegularity) (γ : ℝ)
    (h0 : 0 < γ) (h2 : γ < 2) : LQGMeasureChartStmt γ :=
  lqgMeasureChartStmt_of_openChartProp fun _ _ _ _ hS _ _ hH => hS.ae_openChartProp hE hR h0 h2 hH

/-- **The coordinate change of the LQG measure for all inverse charts** (`LQGMeasureChartStmt γ`, `0 < γ < 2`), from the
one cited input `SheffieldWangEnvelope` (Sheffield–Wang (2016), Theorem 1.1 and the envelope statement at the end of the
proof of Theorem 1.2); the local regularity of the zero-boundary GFF is
`GFFLocalRegularity.zeroBoundaryGFFLocalRegularity`. -/
theorem lqgMeasureChartStmt_of_envelope (hE : SheffieldWangEnvelope) (γ : ℝ) (h0 : 0 < γ) (h2 : γ < 2) :
    LQGMeasureChartStmt γ :=
  lqgMeasureChartStmt_of_inputs hE GFFLocalRegularity.zeroBoundaryGFFLocalRegularity γ h0 h2

end MatedCRT
