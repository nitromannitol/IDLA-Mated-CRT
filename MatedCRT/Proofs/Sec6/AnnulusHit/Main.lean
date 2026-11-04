import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Proofs.Sec6.AnnulusHit.FieldPotential

/-!
# Lemma 6.5 (lemma:annulus-hit, line 2350; event corrected by [C5])

The proof (lines 2358-2385) is `annulusHit_of_steps` (`MatedCRT/Steps/Sec6/AnnulusHit.lean`). Its tightness step
(IR-c4-4, "`L_1(0)/R_1(0)` is a positive finite random variable", line 2384) is proved here from the existence of the
whole-plane LQG measure and its upper volume tail, through the whole-plane field steps of
`MatedCRT/Proofs/Sec6/AnnulusHit/Field*.lean`:
* the law of `E_1(0; C)` is the same for all whole-plane realizations (`Field.wholePlane_goodAnnulus_law`);
* `min_{w ∈ 𝔸_{1,2}} μ(B_{𝐜₀}(w)) > 0` a.s., by full support (`Field.wholePlane_goodAnnulus_denominator_pos_ae`);
* `sup_v ∫_{𝔸_{1,2}} (log (1/|u - v|) + 1) dμ(u) < ∞` a.s. from the volume tail
  (`Field.goodAnnulus_potential_ae_finite_of_volume_tail`);
* hence `P[¬E_1(0; C)] ≤ 1 - p` for `C` large (`Field.wholePlane_goodAnnulus_uniform_of_volume_tail`).

Remaining inputs of Lemma 6.5: `WholePlaneLQGExistenceStep` (IR-c4-1), `ConeWholePlaneWeylComparisonStep` (IR-c4-2),
`WholePlaneLQGCoordinateChangeStep` (IR-c4-3) and `WholePlaneUpperVolumeTailStep` (literature content of IR-c4-4).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- **The tightness step of Lemma 6.5** (IR-c4-4, line 2384) from the existence of a whole-plane LQG measure and the
upper volume tail of whole-plane LQG measures. -/
theorem wholePlaneGoodAnnulusTightness_of_volumeTail (h0 : WholePlaneLQGExistenceStep)
    (hV : WholePlaneUpperVolumeTailStep) : WholePlaneGoodAnnulusTightnessStep := by
  intro γ hγ hγ2 c₀ hc₀ hc₀' p _ hp1
  obtain ⟨Ω, mΩ, P, hC, hcirc, μ, _, hwp, hlqg⟩ := h0 γ hγ hγ2
  obtain ⟨β, q, K, r₀, hβ, hq, hr₀, htail⟩ := hV γ hγ hγ2 Ω P hC hcirc μ hwp hlqg
  obtain ⟨C, hCpos, hCbd⟩ :=
    Field.wholePlane_goodAnnulus_uniform_of_volume_tail hγ hγ2 hwp hlqg hβ hq hr₀ htail hc₀ hc₀' hp1
  exact ⟨C, hCpos, fun Ω' _ P' hC' hcirc' μ' _ hwp' hlqg' => hCbd Ω' P' hC' hcirc' μ' hwp' hlqg'⟩

/-- **Lemma 6.5** (lemma:annulus-hit, line 2350, event corrected by [C5]) from the whole-plane field inputs:
existence of a whole-plane GFF with its LQG measure (IR-c4-1), the Weyl comparison of the cone field with the
whole-plane field near an admissible annulus (IR-c4-2, eq:gff and Weyl scaling), the LQG coordinate change for the
whole-plane field (IR-c4-3, eq:gff-scaling) and the upper volume tail of whole-plane LQG measures. -/
theorem annulusHit_of_volumeTail (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep) : AnnulusHitStmt :=
  annulusHit_of_steps h0 h1 h2 (wholePlaneGoodAnnulusTightness_of_volumeTail h0 hV)

end MatedCRT
