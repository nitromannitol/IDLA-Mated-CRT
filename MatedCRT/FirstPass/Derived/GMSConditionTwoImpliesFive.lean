import MatedCRT.FirstPass.Derived.ZeroConeScalingInvariance
import MatedCRT.FirstPass.Derived.CappedSquareResamplingMassTransport

/-!
# Mass transport for the shifted zero-cone cell configuration

Gwynne, Miller and Sheffield (*An invariance principle for ergodic scale-free random environments*,
arXiv:1807.07515) list equivalent forms of translation invariance modulo scaling of a random cell
configuration `H` (Definition 1.2 and Lemma 2.3). Condition 2 of Definition 1.2, *attainability as a
spatial average of a sample instance modulo scaling*, asks for origin-containing sets `U_n` such that,
with `z_n` sampled uniformly from Lebesgue measure on `U_n`, there are random `C_n > 0` with
`C_n (H - z_n) → H` in law. Appendix B there derives from it Condition 5, the dyadic-system re-sampling
property (paragraph "Condition 2 ⇒ Condition 5").

This file records that implication, for the origin-centred disks `U_n = B_{R_n}(0)` with random radii
`R_n → ∞` almost surely, as the named hypothesis `GMSConditionTwoImpliesFive`, and combines it with
Condition 5 ⇒ Condition 4 (`massTransport_of_cappedSquareResampling`) and with the spatial-average
form of translation invariance modulo scaling verified for the shifted zero-cone configuration (3.1)
of Gwynne–Miller–Sheffield, arXiv:1705.11161 (`ZeroConeSpatialAverageInvariance`): the law of every
realization of the configuration satisfies the mass-transport principle `MassTransport`.

## Main results
* `AttainableAsSpatialAverage μ`: Condition 2 of Definition 1.2 of arXiv:1807.07515, with the
  disks `B_{R_n}(0)`, `R_n → ∞` almost surely.
* `GMSConditionTwoImpliesFive`: Appendix B of arXiv:1807.07515, Condition 2 ⇒ Condition 5.
* `massTransport_of_attainableAsSpatialAverage`: Condition 2 ⇒ Condition 4 under that hypothesis.
* `massTransport_map_of_zeroConeSpatialAverageInvariance`: the mass-transport principle for the
  law of every realization of the shifted zero-cone configuration.
-/

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal BoundedContinuousFunction

/-- **Attainability as a spatial average of a sample instance, modulo scaling** (condition 2 of
Definition 1.2 of Gwynne–Miller–Sheffield, arXiv:1807.07515, for cell configurations), with the
origin-centred disks `U_n = B_{R_n}(0)` and random radii `R_n → ∞` almost surely: `μ` is the law of a
random cell configuration `H` on some probability space, and there are random scale factors
`C_n = exp c_n > 0`, depending on everything and on the sampled point, such that, with `z_n` sampled
uniformly from Lebesgue measure on `B_{R_n}(0)` given everything, `C_n (H - z_n)` converges in law
to `H`: the integral of every bounded continuous function on the GMS space (topology of the metric
`d^CC`) converges. -/
def AttainableAsSpatialAverage (μ : Measure GMSSpace) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (H : Ω → GMSSpace),
    IsProbabilityMeasure P ∧ AEMeasurable H P ∧ P.map H = μ ∧
    ∃ R : ℕ → Ω → ℝ, (∀ n, Measurable (R n)) ∧ (∀ n ω, 0 < R n ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop atTop) ∧
      ∃ c : ℕ → Ω × ReflectedGMS.Plane → ℝ,
        (∀ n, AEMeasurable (fun q => similarityConfig (c n q) q.2 (H q.1)) (P.prod volume)) ∧
        ∀ φ : GMSSpace →ᵇ ℝ, Tendsto
          (fun n => ∫ ω, (⨍ z in Metric.ball (0 : ReflectedGMS.Plane) (R n ω),
            φ (similarityConfig (c n (ω, z)) z (H ω))) ∂P)
          atTop (𝓝 (∫ ω, φ (H ω) ∂P))

/-- **Condition 2 ⇒ Condition 5** of Lemma 2.3 of Gwynne–Miller–Sheffield, arXiv:1807.07515
(Appendix B, paragraph "Condition 2 ⇒ Condition 5", (B.3)–(B.4)), for the origin-centred disks
`U_n = B_{R_n}(0)` with `R_n → ∞` almost surely: the law of a random cell configuration that is
attainable as a spatial average of a sample instance modulo scaling has the dyadic-system
re-sampling property, in the test-function form `CappedSquareResampling`. -/
def GMSConditionTwoImpliesFive : Prop :=
  ∀ μ : Measure GMSSpace, AttainableAsSpatialAverage μ → CappedSquareResampling μ

/-- **Condition 2 ⇒ Condition 4** of Definition 1.2 of arXiv:1807.07515, under Appendix B's
Condition 2 ⇒ Condition 5: the law of a random cell configuration attainable as a spatial average of a
sample instance modulo scaling satisfies the mass-transport principle. -/
theorem massTransport_of_attainableAsSpatialAverage (h25 : GMSConditionTwoImpliesFive)
    {μ : Measure GMSSpace} (h2 : AttainableAsSpatialAverage μ) : MassTransport μ :=
  massTransport_of_cappedSquareResampling (h25 μ h2)

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The shifted zero-cone configuration is attainable as a spatial average modulo scaling**: under
the spatial-average invariance verified in the proof of Proposition 3.1 of arXiv:1705.11161, the law of
every realization of the configuration (3.1) satisfies Condition 2 of Definition 1.2 of
arXiv:1807.07515, on the probability space of the coupling and the phase. -/
theorem attainableAsSpatialAverage_map_of_zeroConeSpatialAverageInvariance
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hI : ZeroConeSpatialAverageInvariance D hγ) {G : Ω → Path2} {F : Ω × ℝ → GMSSpace}
    (hF : IsZeroConeConfigRealization D hγ G F) :
    AttainableAsSpatialAverage ((P.prod zeroConePhase).map F) := by
  have := D.isProbabilityMeasure
  obtain ⟨R, hRm, hRpos, hRlim, c, hcm, hconv⟩ := hI G F hF
  have hR' : ∀ᵐ p ∂P.prod zeroConePhase, Tendsto (fun n => R n p.1) atTop atTop :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := zeroConePhase)).ae hRlim
  exact ⟨Ω × ℝ, inferInstance, P.prod zeroConePhase, F, inferInstance, hF.2.2.1, rfl,
    fun n p => R n p.1, fun n => (hRm n).comp measurable_fst, fun n p => hRpos n p.1, hR', c, hcm,
    hconv⟩

/-- **Translation invariance modulo scaling of the shifted zero-cone configuration, in the
mass-transport form** (hypothesis 1 of Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16, as
verified in arXiv:1705.11161, Proposition 3.1): under the spatial-average invariance of the zero cone
and Appendix B's Condition 2 ⇒ Condition 5, the law of every realization of the configuration (3.1)
satisfies the mass-transport principle (1.3). -/
theorem massTransport_map_of_zeroConeSpatialAverageInvariance
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    {G : Ω → Path2} {F : Ω × ℝ → GMSSpace} (hF : IsZeroConeConfigRealization D hγ G F) :
    MassTransport ((P.prod zeroConePhase).map F) :=
  massTransport_of_attainableAsSpatialAverage h25
    (attainableAsSpatialAverage_map_of_zeroConeSpatialAverageInvariance D hγ hI hF)

end ZeroCone

end MatedCRT
