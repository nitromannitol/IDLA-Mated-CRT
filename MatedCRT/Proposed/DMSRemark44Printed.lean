import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeScale
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRescaleField
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import MarkovProcess.Examples.BrownianMotion
import MarkovProcess.Path.ExitTimeShift
import MatedCRT.Defs.QuantumCone
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLastZeroR

/-!
# DMS Remark 4.4 (pp. 74–75): the printed clauses, staged and not proved

This file stages, as Lean propositions, the two assertions that Duplantier–Miller–Sheffield,
*Liouville quantum gravity as a mating of trees*, arXiv:1409.7055v4 (Remark 4.4, printed pp. 74–75),
makes about the post-last-zero construction of a drifted path:

* `DMS14Remark44PositiveRealization`: the drifted post-last-zero path `X_t = c(ℓ + t)` realizes the
  positive process starting at zero;
* `DMS14Remark44PositiveLevelLaw`: for each level `δ > 0`, the path `(X_{τ_δ + t})_{t ≥ 0}` after the first
  hit `τ_δ` of `δ` has the law of Brownian motion with drift `d` started at `δ`, conditioned never to hit zero.

The printed remark does not state a weak-limit conditioning. The conditioned weak limit
`MatedCRT.IsBMConditionedPositive` is derived in
`MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroShiftedLaw.lean` from these clauses, not ascribed to the
remark. The target `DMS14Remark44PostLastZeroLaw` (`DuplantierMillerSheffieldCone2014.lean`) is not used.

Notation: `c(u) = b(u⁺) + d u`; `ℓ = lastZeroR c` is the last zero of `c` (LatticeProb module
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLastZeroR`, Bonanno's `lastZeroR`); `τ_δ` is the
first passage to `δ` (the exit time from `(-∞, δ)` of the MarkovProcess path library, Armstrong);
Brownian motion is `MarkovProcess.brownianMotion` and the Wiener path law `ProbabilityTheory.IsBrownianReal`
is the Mathlib predicate used by the target.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Proposed

/-- The affine change `t ↦ a + y t + b t` of a real path `y` on `ℝ≥0`: a translation by the constant `a`
and a drift `b`. With `a = δ`, `b = d`, the image of a standard Brownian path `y` is Brownian motion with
drift `d` started at `δ`. -/
def affinePath (a b : ℝ) (y : MarkovProcess.ContinuousPath ℝ) : MarkovProcess.ContinuousPath ℝ :=
  ⟨fun t => a + y t + b * (t : ℝ), (continuous_const.add y.continuous).add
    (continuous_const.mul NNReal.continuous_coe)⟩

/-- The drifted post-last-zero path `X_t = c(ℓ + t)` of DMS Remark 4.4 (pp. 74–75), for the drifted path
`c(u) = b(u⁺) + d u` and `ℓ = lastZeroR c` its last zero (LatticeProb, `MatedCRTHarmonic.MatedCRT.lastZeroR`).
Its undrifted coordinate `X_t - d t` is `dmsPostLastZeroPath d b` in `DuplantierMillerSheffieldCone2014.lean`. -/
noncomputable def dmsDriftedPostLastZeroPath (d : ℝ) (b : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  let c : ℝ → ℝ := fun u => b u.toNNReal + d * u
  let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
  fun t => c (ℓ + t)

/-- The first hitting time `τ_δ` of the level `δ` by a real path, realized as the exit time from `(-∞, δ)`
in the MarkovProcess path library (`MarkovProcess.ContinuousPath.exitTime`, Armstrong), as an element of
`ℝ≥0` (value `0` where the path never reaches `δ`). For a path starting below `δ` it is the first time at
which the path reaches `δ`. -/
noncomputable def dmsFirstLevelHit (δ : ℝ) (y : MarkovProcess.ContinuousPath ℝ) : ℝ≥0 :=
  (MarkovProcess.ContinuousPath.exitTime (Set.Iio δ) y).toNNReal

/-- Brownian motion with drift `d` started at `δ`: the law of `t ↦ δ + W_t + d t` for a standard Brownian
motion `W` started at `0` (`MarkovProcess.brownianMotion 0`). -/
noncomputable def driftedBrownianFrom (d δ : ℝ) : Measure (MarkovProcess.ContinuousPath ℝ) :=
  Measure.map (affinePath δ d) (MarkovProcess.brownianMotion 0)

/-- DMS Remark 4.4, first printed clause (pp. 74–75), for a random path `X` of the drifted post-last-zero
construction: almost surely `X` starts at zero and is positive at every positive time, so the post-last-zero
drifted path realizes the positive process starting at zero. -/
def DMS14Remark44PositiveRealization {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → MarkovProcess.ContinuousPath ℝ) : Prop :=
  ∀ᵐ ω ∂P, X ω 0 = 0 ∧ ∀ t : ℝ≥0, 0 < t → 0 < X ω t

/-- DMS Remark 4.4, second printed clause (pp. 74–75), positive level, for drift `d`: for every level `δ > 0`,
the shifted path `(X_{τ_δ + t})_{t ≥ 0}` after the first hit `τ_δ` of `δ` has the law of Brownian motion with
drift `d` started at `δ`, conditioned never to hit zero. The conditioning is the normalized restriction
`ProbabilityTheory.cond` to the event `{y | ∀ t, y t ≠ 0}`. -/
def DMS14Remark44PositiveLevelLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (d : ℝ)
    (X : Ω → MarkovProcess.ContinuousPath ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    P.map (fun ω => MarkovProcess.ContinuousPath.shift (dmsFirstLevelHit δ (X ω)) (X ω)) =
      ProbabilityTheory.cond (driftedBrownianFrom d δ) {y | ∀ t : ℝ≥0, y t ≠ 0}

/-- DMS Remark 4.4 (pp. 74–75), staged on the canonical Wiener space `W = MarkovProcess.brownianMotion 0`, the
law of a standard Brownian motion on path space (`B_s(ω) = ω s`). For every `0 < γ < 2`, with drift
`d = Q - γ = lqgQ γ - γ > 0`, and every measurable map `F` on path space which equals the drifted post-last-zero
path `dmsDriftedPostLastZeroPath d ω` `W`-almost surely, both printed clauses hold for `F`. No weak-limit conclusion
is printed here, and no transfer from an arbitrary probability space is asserted. -/
def DMS14Remark44PrintedWiener : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ F : MarkovProcess.ContinuousPath ℝ → MarkovProcess.ContinuousPath ℝ, Measurable F →
    (∀ᵐ ω ∂(MarkovProcess.brownianMotion 0), ∀ t : ℝ≥0,
      F ω t = dmsDriftedPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => ω s) t) →
    DMS14Remark44PositiveRealization (MarkovProcess.brownianMotion 0) F ∧
      DMS14Remark44PositiveLevelLaw (MarkovProcess.brownianMotion 0) (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) F

/-- **Residual transfer type, not printed and not proved here.** The clauses of `DMS14Remark44PrintedWiener` for an
arbitrary probability space `(Ω, P)` carrying a Brownian motion `B` (`ProbabilityTheory.IsBrownianReal`, whose
coordinates are only almost-everywhere measurable) and a measurable version `F` of the drifted post-last-zero path.
Passing from the Wiener-space clauses to this form is the arbitrary-space transfer of steps4-r2.tex Section 2
(lines 443–460: measurable rational-time versions, continuous extension, law identification); it is not formalized.
The numbered target `DMS14Remark44PostLastZeroLaw` follows from this Prop by
`MatedCRT.Sec1.dms14Remark44PostLastZeroLaw_of_transferResidual`, a conditional assembly, not a closure. -/
def DMS14Remark44TransferResidual : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (F : Ω → MarkovProcess.ContinuousPath ℝ),
    IsBrownianReal B P → Measurable F →
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      F ω t = dmsDriftedPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => B s ω) t) →
    DMS14Remark44PositiveRealization P F ∧
      DMS14Remark44PositiveLevelLaw P (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) F

end MatedCRT.Proposed
