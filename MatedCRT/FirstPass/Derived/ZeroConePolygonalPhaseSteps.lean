import MatedCRT.FirstPass.Derived.ZeroConePolygonalPremises
import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseBase
import MatedCRT.FirstPass.Derived.CellSideMult

/-!
# The two-clock equality behind the phase periods of the polygonal observables

For the mating-of-trees coupling `D` and a default point `H₀`, `ZeroConePolygonalPhasePeriods D hγ H₀`
(`ZeroConePolygonalPremises.lean`) asks that a bounded similarity-invariant observable of the polygonal configuration
of the zero-cone curve have arbitrarily small periods in the phase. The printed step (Gwynne–Miller–Sheffield,
arXiv:1705.11161v5, proof of Proposition 3.1, p. 23, lines 1193-1196) infers that the observable is a function of the
phase alone from its independence of the field and the curve, which does not follow from independence. The periods come
instead from a comparison of two quantum clocks of the same Lebesgue-parametrized curve `ηL`: adding a smooth bump `g`
to the zero-cone field multiplies its area measure `μ` by `e^g` (`tiltArea g μ`), the tilted clock differs from the old
one by the constants `d_+` and `d_-` on the future and past time tails (`clockOffset`), and the observable of the tilted
curve at the phase `{θ + d_±}` equals the observable of the zero-cone curve at the phase `θ`.

This file states that equality, `ZeroConeTiltPhaseEquality D hγ H₀`, for the observables
`phaseObs Φ H₀ q θ = Φ(polygonalConfig H₀ (q(· + θ), multiplicities of q(· + θ)))`.
-/

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal

/-- The observable `Φ` of the polygonal configuration of the curve `q` read at the phase `θ`: the configuration of the
curve `t ↦ q(t + θ)` with the multiplicities of its cell sides read off the same curve. -/
def phaseObs (Φ : GMSSpace → ℝ) (H₀ : GMSSpace) (q : C(ℝ, ℂ)) (θ : ℝ) : ℝ :=
  Φ (polygonalConfig H₀ (curveTimeTranslate θ q, fun j k => cellSideMult 1 ⇑(curveTimeTranslate θ q) j k))

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The two-clock equality.** For every bounded measurable similarity-invariant observable `Φ`, every smooth `g ≥ 0`
with support in the punctured unit disk and each time tail `b`, almost surely in the sample and the phase `θ`, the
observable
of the curve `ηL` reparametrized by the tilted area measure `e^g μ`, read at the phase `{θ + d_b}`, equals the observable
of the zero-cone curve `η₀` at the phase `θ`; here `μ` is the area measure of the zero-cone field and `d_b` the clock
offset of the tail `b` (`clockOffset`). -/
def ZeroConeTiltPhaseEquality (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) (H₀ : GMSSpace) : Prop :=
  ∀ Φ : GMSSpace → ℝ, Measurable Φ → (∃ M : ℝ, ∀ H, |Φ H| ≤ M) →
    (∀ (s : ℝ) (u) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' → Φ H' = Φ H) →
    ∀ g : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → tsupport g ⊆ Metric.ball (0 : ℂ) 1 \ {0} →
      (∀ z, 0 ≤ g z) → ∀ b : Bool, ∀ᵐ p ∂P.prod zeroConePhase,
        phaseObs Φ H₀
            (massReparamCurve (tiltArea g (ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' p.1))) (ηL p.1))
            (toIcoMod (zero_lt_one' ℝ) 0
              (p.2 + clockOffset g (ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' p.1)) (ηL p.1) b)) =
          phaseObs Φ H₀ (η₀ p.1) p.2

end ZeroCone

end MatedCRT.ZeroConePolygonal
