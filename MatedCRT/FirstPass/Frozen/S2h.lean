import MatedCRT.Defs.Setting
import HarmonicBalls.Defs.Obstacle

/-!
# First-pass frozen external inputs of the cone certificate null hull (fp-S2h, z1)

Each `def` is an EXTERNAL input of `ConeCertificateNullHullStep` (`FirstPass/S2h.lean`), used only as an explicit
hypothesis of `coneCertificateNullHull_of_steps`. Nothing here is proved. None of these statements is about clusters,
odometers, harmonic balls or IDLA processes: each concerns the quantum cone, the whole-plane GFF and the LQG measure
(operator note 2026-11-09 22:53 UTC, item (b)).
-/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- FIRST-PASS FROZEN. Local law of the quantum cone equals the local law of the log-GFF. For `0 < γ < 2` and every
γ-quantum cone field `(P, hC, hcirc, μ)` (`IsConeField`) there is a whole-plane GFF `h^ℂ` on a probability space
`(Ω', P')` whose LQG measure of `h^ℂ − γ log|·|` (`IsLQGMeasureOfField P' γ γ hcirc' μ'`) has the same law as the cone's
measure on `B_1`, tested against any countable family of continuous compactly supported functions supported in `B_1`:
the laws of the moment vectors `ω ↦ (∫ φs k d μ_ω)_k` agree. Sources: Duplantier-Sheffield, "Liouville quantum gravity
and KPZ" (Invent. Math. 2011, arXiv:0808.1560), the quantum cone (Definition 2.1 of arXiv:2211.04891, lines 427-439)
and its restriction to `B_1`; the local equality is the restriction identity used in IDLA eq. (2.4) (arXiv:2211.04891);
GMC locality (the LQG measure on `B_1` is a measurable function of the circle averages on `B_1`, DS 2011 Section 3 /
Kahane 1985). Companion of the frozen `FrozenConeRestriction` (circle averages on `B_1`, `Steps/Sec2`). Locator:
IDLA arXiv:2211.04891, Definition 2.1 (p. 11), (2.4), (2.8) and Fact 2.2(II) (p. 12); DS 2011. Truth check TRUE
(ChatGPT, 23:22 UTC). Used by:
coneCertificateNullHull_of_steps (FirstPass/S2h.lean). -/
def FrozenConeLogLocalCodeLaw : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧ IsLQGMeasureOfField P' γ γ hcirc' μ' ∧
      ∀ φs : ℕ → ℂ → ℝ, (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ Metric.ball 0 1) →
        P.map (fun ω k => ∫ x, φs k x ∂(μ ω)) = P'.map (fun ω k => ∫ x, φs k x ∂(μ' ω))

/-- FIRST-PASS FROZEN. Deterministic least-supersolution membership under two-sided power growth on `B_{3/4}`
(pole `0`, time `t > 0`): if `ν` is a locally finite measure on `ℂ` with `VolumeGrowth ν (3/4) β⁻ β⁺` (the volume
growth condition (A.1) with radius `3/4`), then the least supersolution `leastSupersolution ν (3/4) 0 t` belongs to
`supersolutions ν (3/4) 0 t` for every `t > 0`. Sources: Bou-Rabee and Gwynne, "Harmonic balls in Liouville quantum
gravity", arXiv:2208.11795v3, Appendix A: condition (A.1) (printed p. 65), Lemma A.1 (pp. 66-67) for a general disk
radius (the statement recorded at the beginning of Appendix A.5, p. 70), and the substitution `v = ṽ - q_{B_R}` after
(A.7) (p. 66); Appendix A.5 (p. 70). Truth check TRUE (ChatGPT, 23:22 UTC). This is a deterministic statement about
`Measure ℂ`, not an almost-sure one. Lean counterpart in the
harmonic-balls-lqg repository: `ObstacleLeastSuperharmonicMajorantGeneral` (Steps/SecA) with the substitution
`ObstacleCompatibilityShiftStep`, combined in `leastSupersolution_mem_of_general` (Steps/Sec3/LeastSupersolutionMem).
The printed Draft `ObstacleLeastSuperharmonicMajorantStmt` is the radius-`1` case only. Used by:
`lsoClass_leastSuperOK` and `coneLeastSuperNullHull_proved` (FirstPass/S2h/LeastSuper.lean). -/
def LeastSupersolutionMemOfVolumeGrowthStmt : Prop :=
  ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν → ∀ βminus βplus : ℝ, VolumeGrowth ν (3 / 4) βminus βplus →
    ∀ t : ℝ, 0 < t → leastSupersolution ν (3 / 4) 0 t ∈ supersolutions ν (3 / 4) 0 t

/-- FIRST-PASS FROZEN. Coordinate covariance of the LQG measure of a whole-plane log field under dilation (the GMC change
of coordinates with the random normalization `A_s = exp(γ (Q_γ log s + h_s(0)))`, where `h_s(0)` is the circle average of
the inserted field `h = h^ℂ − γ log|·|` at radius `s` and `0`, i.e. `h_s(0) = h^ℂ_s(0) − γ log s`; equivalently
`A_s = e^{γ h^ℂ_s(0)} s^{2 − γ²/2}`, which is the Lean expression below via `fieldCircleAverage`. Using the circle average
of `h^ℂ` itself, without the `−γ log s`, would be wrong): for `0 < γ < 2`, `s > 0`, a whole-plane
GFF `h^ℂ` (`IsWholePlaneGFF`) and its LQG measure `μ = μ_{h^ℂ − γ log|·|}` (`IsLQGMeasureOfField P γ γ hcirc μ`, with `μ`
AE-measurable as a `Measure ℂ`-valued variable), the random measure `A_s^{-1} · μ(s ·)` has the same law as `μ`. In the
form used: `μ_{h^s}(E) = A_s^{-1} μ_h(sE)` with `h^s = h(s·) − h_s(0)` and `h^s =d h` (CHATGPT-cone-good-set.md (40)-(41)).
Sources: Duplantier and Sheffield, "Liouville quantum gravity and KPZ", Invent. Math. 185 (2011), arXiv:0808.1560, the
coordinate change of the GMC measure (Section 3, locator pending); Bou-Rabee and Gwynne, "Harmonic balls in Liouville
quantum gravity", arXiv:2208.11795v3, Lemma 5.7 (the normalization used in its Draft `ClusterScaleInvarianceStmt`,
HarmonicBalls/Draft/Section5.lean:226; printed page pending). Standard; locator pending. Truth check TRUE as typed, normalization included (ChatGPT, 01:07 UTC,
notes/fp-gaps/CHATGPT-idla-K-S2h-S2k-truth.md §2, §4); it is derivable from `FrozenInsertionCoordinateRule`
(FirstPass/Frozen/S2k.lean) by the decoder argument of §2 and is to be retired when that derivation is written.
Used by: none yet (planned for `HalfPlateauNullStep`, FirstPass/S2h/LogZero.lean). -/
def FrozenWholePlaneLQGScaling : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → AEMeasurable μ P → ∀ s : ℝ, 0 < s →
    P.map (fun ω => ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹ •
      Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω)) = P.map μ

end MatedCRT
