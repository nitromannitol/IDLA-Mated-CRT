import MatedCRT.FirstPass.Derived.ReferenceBoundsForallGamma

/-!
# The last assertion of Lemma 6.13 (Berestycki–Gwynne (2020)) from a reference environment

The binder `hbd` of `hEqLaw_of_scaling` (the quenched walk started within `δ` of the boundary of `B_{1/2}` leaves
`G(B_{1/2})` before hitting the frontier set of `B_{√δ}`, with all visited cells inside that ball, with probability
`≥ 1 - A δ^ξ`, uniformly in valid environments, up to a polynomially small set of environments) is the instance
`ρ = 1/2` of `exitBeforeBallHit_cells_of_reference_of_forall_gamma`.  Its binders are the normalized SLE law and a
reference environment with the mating-rigid set of the transfer, and the cell size estimate (Lemma 2.8).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
/-- **Lemma 6.13, last assertion at `ρ = 1/2`, from a reference environment** (the binder `hbd` of
`hEqLaw_of_scaling`). -/
theorem hbd_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω)
          (ball (0 : ℂ) (1 / 2) \ ball (0 : ℂ) (1 / 2 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}} :=
  MatedCRT.ExitBeforeBallHitEnv.exitBeforeBallHit_cells_of_reference_of_forall_gamma hν hνref href hU h28 γ hγ hγ2
    (1 / 2) (by norm_num) (by norm_num)

end MatedCRT.FirstPass.Derived
