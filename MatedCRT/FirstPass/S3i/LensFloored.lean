import MatedCRT.FirstPass.S3i.FrozenFloored

/-!
# The floored one-sided boundary estimate with the floor exponent fixed before the radius

`FrozenOneSidedBoundaryContinuityFloored` (S3i/FrozenFloored.lean) chooses the floor exponent `β` after
`ρ`, `Ω` and `S`. `FrozenOneSidedBoundaryContinuityFlooredUniform` below chooses `β` before `ρ`, `Ω` and `S`
(the quantifier order of `QuenchedLensStep`, S3i/Proof.lean:240, for the exponent `b` of the lens step).

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv:1807.07511v3, Theorem 3.9,
equation (3.31) and its proof on p. 32, with Lemma 3.11 (p. 31). Quoted from
the campaign record of the GMS extraction (MQ-li-7 (a)):

* (3.31), p. 30: "If D is simply connected, then we also have the boundary continuity estimate
  min_{y∈VGε(∂D∩Bt(η(x)))} fε(y) − A‖fε‖∞ (t/dist(η(x),∂D))^{−ξ} ≤ fε(x) ≤ max_{y∈VGε(∂D∩Bt(η(x)))} fε(y)
  + A‖fε‖∞ (t/dist(η(x),∂D))^{−ξ}, ∀x ∈ VGε(D), ∀t > 0."
* Lemma 3.11, p. 31: "For each ρ ∈ (0, 1), there exists α = α(γ) > 0, β = β(γ) > 0, and p = p(ρ, γ) > 0 such that for
  each ε ∈ (0, 1), the following holds with probability 1 − Oε(ε^α). For each z ∈ Bρ(0) and each r ∈ [ε^β, ρ] with
  B2r(z) ⊂ Bρ(0), min_{x∈VGε(Br(z))} Pεx[Xε disconnects VGε(∂Br/2(z)) from VGε(∂B2r(z)) before hitting VGε(∂B2r(z))]
  ≥ p. (3.35)"
* Proof of (3.31), p. 32: "By applying the Markov property of Xε and (3.35) with r = e^{−k} for k ∈ [⌈log t^{−1}⌉,
  ⌊log(2 dist(η(x),∂D))^{−1}⌋], we get that for t > 2 dist(η(x),∂D), Pεx[Xε first hits VGε(∂D) at a point in
  VGε(∂D∩Bt(η(x)))] ≥ 1 − p^{log(t/dist)−2} ≥ 1 − A (t/dist(η(x),∂D))^{−ξ} (3.38) ... (the case t < 2 dist(η(x),∂D)
  can be dealt with by increasing A)."

The sentence of the p. 32 proof that fixes `β` before `ρ` is NOT in that extraction: the quoted (3.38) sentence does
not mention `β`. The ordering used here rests on the notation of Lemma 3.11, where `β = β(γ)` and only `p = p(ρ, γ)`
carries `ρ`. The printed (3.31) has no floor; the floor `ε ^ β` is the one of the proof (MATH-ANSWERS MQ-li-7 (a)).
PENDING TRUTH CHECK (docs/campaign/FROZEN-PROVENANCE.md): the uniform form is TRUE per MQ-li-7 (a) and MQ-li-9 only
if `β(γ)` is uniform in `ρ`, which the extraction supports by notation alone.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **(BE-floored-uniform)**, the floored one-sided boundary continuity estimate with the floor exponent `β`
chosen before `ρ`, `Ω` and `S`. The body is that of `FrozenOneSidedBoundaryContinuityFloored`
(S3i/FrozenFloored.lean:34-44) with the existential over `β` moved in front of `∀ ρ`.
Such a `β` is the one of GMS Lemma 3.11 (p. 31), which depends on `γ` only; see the module docstring for the
extraction and its gap. PENDING TRUTH CHECK. -/
def FrozenOneSidedBoundaryContinuityFlooredUniform (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ β < 1 ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ κ ν A b : ℝ, 0 < κ ∧ 0 < ν ∧ 0 < A ∧ 0 < b ∧
  PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D → SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f x = 0) →
    ∀ x ∈ interiorCellVertices ε (S.η ω) D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε (S.η ω) D f x t
        + A * discreteSupNorm ε (S.η ω) D f
          * (t / max (infDist (vertexPoint ε (S.η ω) x) (frontier D)) (ε ^ β)) ^ (-ν)}

/-- The quantifier swap: the uniform form implies the floored form of S3i/FrozenFloored.lean, with the same
`β` (the `β` of the uniform form is a valid floor exponent for every `ρ`, `Ω`, `S`). -/
theorem frozenOneSidedBoundaryContinuityFloored_of_uniform {𝒮 : SpaceFillingSLEModel}
    (hU : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    FrozenOneSidedBoundaryContinuityFloored 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS
  obtain ⟨β, hβ0, hβ1, hbody⟩ := hU γ hγ0 hγ2
  obtain ⟨κ, ν, A, b, hκ, hν, hA, hb, hP⟩ := hbody ρ hρ0 hρ1 Ω S hS
  exact ⟨κ, ν, A, b, β, hκ, hν, hA, hb, hβ0, hβ1, hP⟩

end FirstPass36
end MatedCRT
