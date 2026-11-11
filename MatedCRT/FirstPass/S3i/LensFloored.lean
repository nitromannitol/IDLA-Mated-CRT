import MatedCRT.FirstPass.S3i.FrozenFloored
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3i.Proof

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

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
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

/-- **Floored deterministic one-sided boundary estimate at one mesh.** This is `FP36OneSidedBEAt`
(S3i/LensDefs.lean:54) with the vertex restricted to the interior cell vertices and the boundary distance
replaced by its floor `max (infDist …) (ε ^ β)`, as in the body of `FrozenOneSidedBoundaryContinuityFloored`. -/
def FP36OneSidedBEFlooredAt (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ ν A β : ℝ) : Prop :=
  ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D → SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε η D, matedLaplacian m f x = 0) →
    ∀ x ∈ interiorCellVertices ε η D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε η D f x t
        + A * discreteSupNorm ε η D f
          * (t / max (infDist (vertexPoint ε η x) (frontier D)) (ε ^ β)) ^ (-ν)

/-- The floored analogue of `FP36GoodEnv` (S3i/LensDefs.lean:70): the same clauses, with the one-sided boundary
clause replaced by `FP36OneSidedBEFlooredAt` at the floor exponent `β`. -/
def FP36GoodEnvFloored {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ₀ ρ₁ b ν A β r : ℝ)
    (z y : ℂ) (ε : ℝ) (ω : Ω) : Prop :=
  let η := S.η ω
  let m := S.mult ε ω
  IsAreaParametrized (S.μ ω) η ∧
  (∀ j k : ℤ, m j k ≠ 0 →
    (cell ε η j ∩ cell ε η k).Nonempty) ∧
  (∀ k : ℤ, (cell ε η k ∩ ball 0 ρ₁).Nonempty →
    diam (cell ε η k) ≤ ε ^ b) ∧
  (∀ U : Set ℂ, closure U ⊆ ball 0 ρ₀ →
    FiniteExitData m (cellVertices ε η U) ∧
    FiniteExitData m (interiorCellVertices ε η U)) ∧
  vertexOf ε η y ∈
    interiorCellVertices ε η (ball z r) ∧
  FP36OneSidedBEFlooredAt m ε η ρ₁ ν A β

/-- **Floored deterministic core (MQ-li-9 steps 2-3).** The floored analogue of `lensProb_le_of_BE_fp36`
(S3i/LensBE.lean:24). With `b ≤ β` and `ε ≤ 1`, the floor satisfies `ε ^ β ≤ ε ^ b`, so the denominator
`max (d, ε ^ β)` is at most `6 ε ^ b` whenever `d ≤ 6 ε ^ b`, and the exponent algebra of `boundary_power_le_fp36`
applies with `d' := max d (ε ^ β)`. -/
lemma lensProb_le_of_BE_fp36_floored
    {m : ℤ → ℤ → ℕ} {ε ρ₁ b ν A β : ℝ} {η : ℝ → ℂ} {U : Set ℂ} {v : ℤ} {f : ℤ → ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hν : 0 < ν) (hA : 0 < A) (hβb : b ≤ β)
    (hBE : FP36OneSidedBEFlooredAt m ε η ρ₁ ν A β)
    (hUρ : U ⊆ ball 0 ρ₁) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hUsc : SimplyConnectedSpace U)
    (hvU : v ∈ interiorCellVertices ε η U)
    (hrange : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hharm : ∀ x ∈ interiorCellVertices ε η U, matedLaplacian m f x = 0)
    (hbdry : ∀ k ∈ cellVertices ε η (frontier U ∩ ball (vertexPoint ε η v) (ε ^ (b / 2) / 16)), f k = 0)
    (hpos : 0 < infDist (vertexPoint ε η v) (frontier U))
    (hle : infDist (vertexPoint ε η v) (frontier U) ≤ 6 * ε ^ b) :
    f v ≤ A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by
  have hsup0 : boundarySupNear ε η U f v (ε ^ (b / 2) / 16) = 0 := by
    unfold boundarySupNear
    exact le_antisymm
      (Real.iSup_le (fun k => Real.iSup_le (fun hk => (hbdry k hk).le) le_rfl) le_rfl)
      (Real.iSup_nonneg (fun k => Real.iSup_nonneg (fun hk => (hbdry k hk).ge)))
  have hdisc : discreteSupNorm ε η U f ≤ 1 := by
    unfold discreteSupNorm
    exact Real.iSup_le
      (fun k => Real.iSup_le (fun _ => abs_le.2 ⟨by linarith [(hrange k).1], (hrange k).2⟩) zero_le_one)
      zero_le_one
  have hεβ : ε ^ β ≤ ε ^ b := Real.rpow_le_rpow_of_exponent_ge hε hε1 hβb
  have hεb0 : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le b
  have hmaxpos : 0 < max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β) :=
    lt_max_of_lt_left hpos
  have hmaxle : max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β) ≤ 6 * ε ^ b :=
    max_le hle (by linarith)
  have hbe : f v ≤ boundarySupNear ε η U f v (ε ^ (b / 2) / 16)
      + A * discreteSupNorm ε η U f
        * ((ε ^ (b / 2) / 16) / max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β)) ^ (-ν) :=
    hBE U f hUρ hUopen hUconn hUsc hharm v hvU (ε ^ (b / 2) / 16)
        (div_pos (Real.rpow_pos_of_pos hε _) (by norm_num))
  have hpow := boundary_power_le_fp36 (ε := ε) (b := b) (ν := ν) (c := 16) (K := 6)
    (t := ε ^ (b / 2) / 16) hε hν (by norm_num) (by norm_num) hmaxpos hmaxle (le_refl _)
  rw [show ((16 : ℝ) * 6) = 96 by norm_num] at hpow
  have hX : 0 ≤ ((ε ^ (b / 2) / 16) / max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β)) ^ (-ν) :=
    Real.rpow_nonneg (div_nonneg (div_nonneg (Real.rpow_nonneg hε.le _) (by norm_num)) hmaxpos.le) _
  rw [hsup0, zero_add] at hbe
  calc f v ≤ A * discreteSupNorm ε η U f
        * ((ε ^ (b / 2) / 16) / max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β)) ^ (-ν) := hbe
    _ ≤ A * 1 * ((ε ^ (b / 2) / 16) / max (infDist (vertexPoint ε η v) (frontier U)) (ε ^ β)) ^ (-ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdisc hA.le) hX
    _ ≤ A * 1 * ((96 : ℝ) ^ ν * ε ^ (ν * b / 2)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hA.le zero_le_one)
    _ = A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by ring

end FirstPass36
end MatedCRT
