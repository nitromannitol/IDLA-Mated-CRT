import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeScale
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRescaleField
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import MarkovProcess.Examples.BrownianMotion

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
cone. Those identifications remain separate proof obligations. Lemma 4.9 and
Remark 4.4 themselves are not separately formalized here.
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

end MatedCRT.Proposed
