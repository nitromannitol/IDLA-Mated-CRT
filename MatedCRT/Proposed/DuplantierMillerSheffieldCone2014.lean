import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeScale
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRescaleField
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import MarkovProcess.Examples.BrownianMotion
import MatedCRT.Defs.QuantumCone
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLastZeroR

/-!
# Staged cone scaling input

This file stages a distribution-valued instance of Duplantier–Miller–Sheffield,
*Liouville quantum gravity as a mating of trees*, arXiv:1409.7055v4,
Proposition 4.13(i), p. 80, proof p. 81. It is a proposition to be
source-checked by the operator, not a theorem or an axiom.

The cone is built using Definition 4.10, p. 79, and the post-last-zero
construction in Remark 4.4, pp. 74–75. The field uses the radial and lateral
projections described in Lemma 4.9, p. 79. The Brownian motions and the
whole-plane GFF are independent. The radius is the largest circle-average
embedding radius, expressed in logarithmic radial coordinates.

This staging does not assert that the weak-limit conditioning convention in
`MatedCRT.IsBMConditionedPositive` agrees with the post-last-zero construction,
or that the observable cone predicate represents this distribution-valued
cone. Those identifications remain separate proof obligations. Remark 4.4 is staged below as the explicit cited Prop
`DMS14Remark44PostLastZeroLaw`, not proved. Lemma 4.9 is not formalized here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Proposed

/-- Radius which restores the circle-average embedding after adding `C / γ`. -/
def dmsConeEmbeddingRadius (γ α C : ℝ) (B B' : ℝ≥0 → ℝ) : ℝ :=
  Real.exp (sSup {s : ℝ |
    MatedCRTHarmonic.MatedCRT.coneLogRadial γ α B B' s = -C / γ})

/-- The DMS additive parameter `C = -log b` gives the paper's cone scale. -/
theorem dmsConeEmbeddingRadius_neg_log (γ α b : ℝ) (B B' : ℝ≥0 → ℝ) :
    dmsConeEmbeddingRadius γ α (-Real.log b) B B' =
      MatedCRTHarmonic.MatedCRT.coneScale γ α B B' b := by
  simp [dmsConeEmbeddingRadius, MatedCRTHarmonic.MatedCRT.coneScale,
    div_eq_mul_inv, mul_comm]

/-- The corresponding re-embedded field is the paper's rescaled field. -/
theorem dmsConeEmbedding_neg_log (γ α b : ℝ) (B B' : ℝ≥0 → ℝ)
    (H : LQGMetric.DistC) :
    LQGMetric.addConst
      (LQGMetric.affineComp (dmsConeEmbeddingRadius γ α (-Real.log b) B B') 0 H)
      (MatedCRTHarmonic.MatedCRT.lqgQ γ *
        Real.log (dmsConeEmbeddingRadius γ α (-Real.log b) B B') + (-Real.log b) / γ) =
      MatedCRTHarmonic.MatedCRT.coneRescaleField γ
        (MatedCRTHarmonic.MatedCRT.coneScale γ α B B' b) b H := by
  rw [dmsConeEmbeddingRadius_neg_log]
  unfold MatedCRTHarmonic.MatedCRT.coneRescaleField
  congr 1
  simp only [div_eq_mul_inv]
  ring

/-- DMS Proposition 4.13(i), for the explicit post-last-zero construction of
an `α`-quantum cone, with `α < Q` and arbitrary area multiplier `exp C`.
The equality is of laws of distributions in the circle-average embedding. -/
def DMS14ConeScaling : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < MatedCRTHarmonic.MatedCRT.lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
    LQGMetric.IsWholePlaneGFF X P → IsBrownianReal B P → IsBrownianReal B' P →
    IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P →
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P →
  ∀ C : ℝ,
    let H : Ω → LQGMetric.DistC := fun ω =>
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ α (fun t => B t ω) (fun t => B' t ω))
    let R : Ω → ℝ := fun ω =>
      dmsConeEmbeddingRadius γ α C (fun t => B t ω) (fun t => B' t ω)
    P.map (fun ω => LQGMetric.addConst (LQGMetric.affineComp (R ω) 0 (H ω))
      (MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log (R ω) + C / γ)) = P.map H

/-- The explicit post-last-zero construction of DMS Remark 4.4 (pp. 74–75): the drifted path
`c u = b(u⁺) + d u` is taken after its last zero `ℓ`, and the drift is subtracted again. This is
`MatedCRT.Sec1.referenceConeConditionedPath` (CanonicalConeIdentification.lean), restated here to
avoid an import cycle (FieldAssembly imports this file). -/
def dmsPostLastZeroPath (d : ℝ) (b : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  let c : ℝ → ℝ := fun u => b u.toNNReal + d * u
  let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
  fun t => c (ℓ + t) - d * t

/-- The drift `lqgQ γ - γ = 2/γ - γ/2` of the conditioned Brownian motion is positive for
`0 < γ < 2`. -/
theorem lqgQ_sub_pos_of_lt_two {γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) :
    0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ := by
  unfold MatedCRTHarmonic.MatedCRT.lqgQ
  have key : 2 / γ + γ / 2 - γ = (4 - γ ^ 2) / (2 * γ) := by
    field_simp
    ring
  rw [key]
  apply div_pos
  · nlinarith
  · positivity

/-- **Staged cited input, not proved.** DMS Remark 4.4, pp. 74–75 (arXiv:1409.7055v4): for a
standard Brownian motion `B` on a probability space and drift `d = lqgQ γ - γ` (`0 < γ < 2`, so
`d > 0`), every measurable continuous-path version `F` of the post-last-zero process
`dmsPostLastZeroPath d (B · ω)` has the weak-limit conditioned law `IsBMConditionedPositive d` of
Definition 2.1 of the paper. Operator to verify this against the DMS text before use.
Caution: env-steps.tex:217–242 cites this remark for the conditioned-law identification and does
not prove it; m1 (reports/m1.md) read Remark 4.4 as a description of the post-last-zero
construction only. -/
def DMS14Remark44PostLastZeroLaw : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (F : Ω → MarkovProcess.ContinuousPath ℝ),
      IsBrownianReal B P → Measurable F →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        F ω t = dmsPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => B s ω) t) →
      MatedCRT.IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F)

end MatedCRT.Proposed
