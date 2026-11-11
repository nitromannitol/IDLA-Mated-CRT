import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S7x
import MatedCRT.External.SLE

/-!
# Lemma 7.4, corrected statement (correction [C25])

The corrected draft `paper/idla_mated_crt-corrected.tex` restates Lemma 7.4 (`lemma:crude-upper-bound`, Levine-Peres
2009, Lemma 4.2) at lines 4027-4035. Two changes, both from [C25]: the increasing path starts in the positive stopped
support `Λ^ε_t = {u^ε_t > 0}` (`matedDiscreteCluster`), minus the origin, and one event of polynomially high
probability serves every `t > 0` at once. `CrudeUpperBoundStmt` (MatedCRT/Draft/Section7.lean:67) is left untouched; it
has `∀ t > 0` outside `PolyHighProb`, and the corrected statement implies it (`crudeUpperBoundStmt_of_corrected`).

Route of the closed proof (the corrected proof of Lemma 7.4 in the same subsection):
* eq:degree-bound, the degree bound `max_{V^ε(B_ρ)} deg^ε ≤ (log ε⁻¹)²`: the literature input `DegreeBoundInput`
  (MatedCRT/External/SLE.lean, GMS19 Lemma 2.6), a hypothesis of `closed_7_4_corrected`;
* eq:laplacian-of-uteps, `Δ^ε u^ε_t = (deg^ε)⁻¹` on `Λ^ε_t \ {0}`: the corrected Lemma 4.4, proved as
  `firstPass_4_4_corrected` (MatedCRT/FirstPass/S3S4.lean), through `stoppedOdometerLaplacianStep_of_corrected`
  (MatedCRT/Proofs/Sec7/OdometerBoundMass/Corrected.lean);
* local finiteness of the map: `adjacentCellsMeetAeStep` (MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean), proved;
* the path: greedy steps to a neighbour maximising `u^ε_t`, induction inside `Λ^ε_t`, termination at `0` by the
  finiteness of `Λ^ε_t`, is `crudeUpperBoundSupport_of_mapSteps` and `crudeUpperBoundSupport_of_corrected`
  (MatedCRT/FirstPass/S7x.lean).

Nothing in the chain is a further paper step without a proof, so no Prop stands for a paper step.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Lemma 7.4, corrected** (`lemma:crude-upper-bound`, `paper/idla_mated_crt-corrected.tex` lines 4027-4035, correction
[C25]; Levine-Peres 2009, Lemma 4.2). Quoted: "With polynomially high probability as `ε → 0`, the following holds
simultaneously for every `t > 0`. For every point `a ∈ Λ^ε_t \ {0}` there is a path `a = a₀ ∼ a₁ ∼ ⋯ ∼ a_m = 0` in
`Λ^ε_t` with `u^ε_t(a_{i+1}) ≥ u^ε_t(a_i) + log(ε⁻¹)⁻²`", where `Λ^ε_t = {u^ε_t > 0}` is the positive stopped support.
The single event `{ω | ∀ t > 0, …}` lies inside `PolyHighProb`. -/
def CrudeUpperBoundCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ t : ℝ, 0 < t → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t \ {0},
    ∃ p : List ℤ, IsVPathIn (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) p a 0 ∧
    p.IsChain fun c d => stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t d}

/-- **Lemma 7.4, corrected, closed.** The corrected Lemma 4.4 and `AdjacentCellsMeetAeStep` are proved; the degree bound
`DegreeBoundInput` (eq:degree-bound, GMS19 Lemma 2.6) is the only hypothesis, and it is a literature input. -/
theorem closed_7_4_corrected {𝒮 : SpaceFillingSLEModel} (hdeg : DegreeBoundInput 𝒮) :
    CrudeUpperBoundCorrectedStmt 𝒮 :=
  crudeUpperBoundSupport_of_corrected 𝒮 (firstPass_4_4_corrected 𝒮) hdeg

/-- The corrected statement implies the Draft statement `CrudeUpperBoundStmt` (Draft, Section 7): for each `t > 0` the
corrected event is contained in the event of `CrudeUpperBoundStmt` for that `t`, and `PolyHighProb` is monotone. So a
consumer of `CrudeUpperBoundStmt` can be given the corrected statement instead. -/
theorem crudeUpperBoundStmt_of_corrected {𝒮 : SpaceFillingSLEModel} (h : CrudeUpperBoundCorrectedStmt 𝒮) :
    CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_support 𝒮 h

end MatedCRT
