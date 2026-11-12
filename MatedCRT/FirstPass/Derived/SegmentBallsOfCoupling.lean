import MatedCRT.FirstPass.Derived.GreenCrudeAE

/-!
# The segment-ball estimate from the mating-of-trees coupling

The segment-ball event `E_ε(2, r)` of Gwynne-Holden-Miller (Prop. 3.4 with Remark 3.9: the failure
probability is `o^∞(ε)`) for the space-filling curve `η` of a valid environment has polynomially
high probability. The estimate is the field `segmentsContainBalls` of the mating-of-trees coupling
`IsMatingOfTreesCoupling` carried by `MatedCRTEnv.IsValid.matingOfTrees`, stated there for the
Lebesgue-parametrized curve `ηL`; the curve `η` is `ηL` reparametrized by an order isomorphism of
`ℝ` (field `areaParam`), and the segment images `η([a, b])` are segment images of `ηL`.

Consequence: `GreenFunctionCrudeBoundStmt` follows from the cell size estimate, the degree bound
and the segment reachability event for almost every direction alone
(`greenFunctionCrudeBoundStmt_of_reachableAE`).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- The segment-ball property is invariant under reparametrization by an order isomorphism of `ℝ`:
if `η = c ∘ φ`, every segment `η([a, b])` is the segment `c([φ a, φ b])`. -/
theorem segmentBall_of_comp_orderIso {c : C(ℝ, ℂ)} {η : ℝ → ℂ} {φ : ℝ ≃o ℝ}
    (hη : ∀ t, η t = c (φ t)) {R r ε : ℝ}
    (h : MatedCRTHarmonic.MatedCRT.SegmentsContainBalls c R r ε) :
    ∀ t ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball 0 R →
      t ^ (1 - r) ≤ diam (η '' Icc a b) → ∃ w : ℂ, ball w t ⊆ η '' Icc a b := by
  intro t ht a b hab
  have himg : η '' Icc a b = c '' Icc (φ a) (φ b) := by
    rw [← φ.image_Icc, image_image]
    exact image_congr fun s _ => hη s
  rw [himg]
  exact h t ht (φ a) (φ b) (φ.lt_iff_lt.2 hab)

/-- **The segment-ball estimate** (Gwynne-Holden-Miller, Prop. 3.4 and Remark 3.9) for the curve of
a valid environment: for every `r ∈ (0, 1)` the event `E_ε(2, r)` has polynomially high
probability. From the field `segmentsContainBalls` of the mating-of-trees coupling. -/
theorem MatedCRTEnv.IsValid.polyHighProb_segmentBallEvent {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : PolyHighProb S.P (S.segmentBallEvent r) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcoup, hae⟩ := hS.matingOfTrees
  obtain ⟨C, hC⟩ := hcoup.segmentsContainBalls 2 two_pos r hr 1
  have hbase : PolyHighProb S.P fun ε =>
      {ω | MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (ηL ω) 2 r ε} := by
    refine ⟨1, one_pos, C, 1, one_pos, fun ε hε hε1 => ?_⟩
    have h := hC ε ⟨hε, hε1⟩
    rw [Real.rpow_one]
    rw [pow_one] at h
    exact h
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | ∀ ε : ℝ,
      MatedCRTHarmonic.MatedCRT.SegmentsContainBalls (ηL ω) 2 r ε →
        ω ∈ S.segmentBallEvent r ε} := by
    filter_upwards [hae, hcoup.areaParam] with ω hω hpar
    obtain ⟨φ, -, hφ⟩ := hpar.1
    exact fun ε hε => segmentBall_of_comp_orderIso
      (fun t => (congrFun hω.1 t).symm.trans (hφ t)) hε
  exact (hbase.inter_ae hW).mono fun ε ω hω => hω.2 ε hω.1

/-- **The crude Green function bound from segment reachability.** `GreenFunctionCrudeBoundStmt`
from the cell size estimate, the degree bound and, for every `ρ ∈ (0, 1)`, the segment
reachability event for almost every direction with polynomially high probability. The
segment-ball estimate is supplied by `MatedCRTEnv.IsValid.polyHighProb_segmentBallEvent`. -/
theorem greenFunctionCrudeBoundStmt_of_reachableAE {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hR : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ U : ℝ, 0 ≤ U ∧ PolyHighProb S.P (S.segmentReachEventAE ρ U)) :
    GreenFunctionCrudeBoundStmt 𝒮 :=
  greenFunctionCrudeBoundStmt_of_segmentBalls_of_reachableAE hcell hdeg
    (fun _ _ _ _ _ _ hS _ hr => hS.polyHighProb_segmentBallEvent hr) hR

end MatedCRT
