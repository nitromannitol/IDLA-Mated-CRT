import MatedCRT.Draft.Section2
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Sec2.ConeHarmonicBallsUpToFixedTime.WholePlane
import MatedCRT.Proofs.Sec2.ConeFamily
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.External.QuantumCone
import MatedCRT.FirstPass.Frozen.S2b

/-!
# First pass, wave 2: Lemmas 2.4 and 2.5 in their printed form (q1)

* `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`: corrected Lemma 2.4 (paper line 533). Existence of `T > 0` and a family
  `{Λ_t}_{0<t<T}` with the properties of Theorem 2.3 stopped at `∂B_{1/2}`, and uniqueness of the family on `(0, T)`.
  The Draft clause `T' = T` (Draft `ConeHarmonicBallsUpToFixedTimeStmt`, Section2.lean:66-72) is NOT in the corrected
  statement: it asserts that the stopping time is unique among all stopped families, which needs strict growth of the
  harmonic balls (`ConeHarmonicBallStrictGrowthStep`, an open problem, REDUCTIONS F14; operator ruling 2026-11-09 17:00).
  The printed proof (line 533-541) only gives uniqueness of the family on the fixed interval (Prop 5.6 of HB22).
* `ConeScaleInvarianceUpToFixedTimeCorrectedStmt`: Lemma 2.5 (paper line 548), existence and uniqueness on `(0, bT^b)`
  of the rescaled family. The Draft clause `T' = Tb ∧ EqOn ...` is dropped for the same reason. The joint law of the
  printed statement (second display, line 552-553) is NOT in this file: it needs a measurable functional of the field
  for the stopped family, which needs uniqueness of the stopping time (closure route, OPEN; see reports/q1.md).
* `firstPass_2_4_corrected`, `firstPass_2_5_corrected`: the first-pass theorems. Hypotheses: Draft statements of the
  Harmonic-Balls numbered results cited by the paper (HB22 Theorems 1.1, 5.5, Lemma 3.2 and their listed inputs) and the
  frozen EXTERNAL inputs of `MatedCRT/FirstPass/Frozen/S2b.lean`, plus `QuantumConeScalingInput` and `LQGMeasurePropertiesStmt`
  (Fact 2.2, cited).

No strict growth of harmonic balls is assumed anywhere in this file.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

namespace MatedCRT

/-- **Corrected Lemma 2.4** (printed text: "On an event of probability one, there exists a unique family of harmonic
balls `{Λ_t}_{0<t<T}` which satisfies the properties of Theorem 2.3 (with `t` restricted to be in `(0,T)`), where
`T = sup {t > 0 : Λ_t ⊂ B_{1/2}}`"; paper lines 533-537). Formal reading: a.s. there are `T > 0` and `Λ` with the
properties of Theorem 2.3 on `(0, T)` (`IsConeHarmonicBallFamilyOn`) which is stopped at `∂B_{1/2}` (`IsStoppedAtHalfBall`:
`Λ_t ⊂ B_{1/2}` for `t < T` and `T` is the supremum), and every family with the properties on `(0, T)` agrees with `Λ` there.
The uniqueness of the stopping time (Draft `T' = T`) is not included: see the module docstring. -/
def ConeHarmonicBallsUpToFixedTimeCorrectedStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∃ Λ : ℝ → Set ℂ,
    IsConeHarmonicBallFamilyOn (μ ω) Λ T ∧ IsStoppedAtHalfBall Λ T ∧
    ∀ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ' T → EqOn Λ' Λ (Ioo 0 T)

/-- **Corrected Lemma 2.5** (printed text: "A.s., there exists a unique family of harmonic balls `{Λ^b_t}_{0<t<bT^b}`
for `μ_h` satisfying the properties of Theorem 2.3 on `(0, bT^b)`, where `T^b = sup {t > 0 : R_b⁻¹ Λ^b_{bt} ⊂ B_{1/2}}`";
paper lines 548-553, first assertion). Formal reading: for `b > 0` there are random `Tb > 0` and `Λb` such that a.s.
`Λb` is a family with the properties of Theorem 2.3 on `(0, b Tb)` whose rescaling `R_b⁻¹ Λ_{bt}` (`rescaledFamily`, with
`R_b` the cone scale radius) is stopped at `∂B_{1/2}` at `Tb`, and every family with the properties on `(0, b Tb)` agrees
with `Λb` there. The joint-law display of the printed lemma is not included (see the module docstring). -/
def ConeScaleInvarianceUpToFixedTimeCorrectedStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b →
    ∃ (Tb : Ω → ℝ) (Λb : Ω → ℝ → Set ℂ),
      ∀ᵐ ω ∂P, 0 < Tb ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λb ω) (b * Tb ω) ∧
        IsStoppedAtHalfBall (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω) ∧
        ∀ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ' (b * Tb ω) → EqOn Λ' (Λb ω) (Ioo 0 (b * Tb ω))

/-- Deterministic transfer of a stopped family through the cone rescaling (printed proof of Lemma 2.5, lines 566-584):
a family `Λ` for the rescaled measure `R_b`-`b`-rescaling of `μ`, stopped at `∂B_{1/2}` at `T`, gives after the inverse
rescaling `R⁻¹`, `b⁻¹` a family for `μ` on `(0, bT)`, stopped at `T` for the rescaled family, and unique on `(0, bT)`. -/
theorem rescaledFamily_transfer {μ : Measure ℂ} {R b T : ℝ} {Λ : ℝ → Set ℂ} (hR : 0 < R) (hb : 0 < b)
    (h : IsConeHarmonicBallFamilyOn (rescaledMeasure μ R b) Λ T) (hst : IsStoppedAtHalfBall Λ T) :
    IsConeHarmonicBallFamilyOn μ (rescaledFamily Λ R⁻¹ b⁻¹) (b * T) ∧
      IsStoppedAtHalfBall (rescaledFamily (rescaledFamily Λ R⁻¹ b⁻¹) R b) T ∧
      ∀ Λ'' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn μ Λ'' (b * T) →
        EqOn Λ'' (rescaledFamily Λ R⁻¹ b⁻¹) (Ioo 0 (b * T)) := by
  have h1 : IsConeHarmonicBallFamilyOn (rescaledMeasure μ R b) Λ (b⁻¹ * (b * T)) := by
    rwa [inv_mul_cancel_left₀ hb.ne']
  have h2 := coneHarmonicBallFamilyOnScalingStep (rescaledMeasure μ R b) Λ R⁻¹ b⁻¹ (b * T)
    (inv_pos.2 hR) (inv_pos.2 hb) h1
  rw [rescaledMeasure_rescaledMeasure_inv μ hR.ne' hb] at h2
  refine ⟨h2, ?_, fun Λ'' hΛ'' => ?_⟩
  · rw [rescaledFamily_rescaledFamily_inv Λ hR.ne' hb.ne']
    exact hst
  · have := h2.eqOn hΛ''
    rwa [min_self] at this

/-- **Corrected Lemma 2.4 from the inputs** (printed proof, lines 533-541): the existence of a stopped family follows from
the whole-plane case (HB22 Theorems 1.1, 5.5, Lemma 3.2 through `wholePlaneHalfBallFamilyStep_of_hb`), eq:gff and the
locality of harmonic balls; uniqueness on `(0, T)` is `IsConeHarmonicBallFamilyOn.eqOn` (HB22 Proposition 5.6 for families
on a fixed interval). No strict growth is used. -/
theorem coneHarmonicBallsUpToFixedTimeCorrected_of_inputs
    (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0})
    (h0 : FrozenWholePlaneLogLQGExistence) (h3 : FrozenConeRestriction)
    (h4 : FrozenConeHarmonicBallLocality) : ConeHarmonicBallsUpToFixedTimeCorrectedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  have hwp := wholePlaneHalfBallFamilyStep_of_hb h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58
  filter_upwards [ae_hasConeHarmonicBallsUpToHalfBall_of_wholePlane h0 hwp h3 h4 hγ0 hγ2 hcone] with ω hω
  obtain ⟨T, hT, Λ, hΛ, hst⟩ := hω
  refine ⟨T, hT, Λ, hΛ, hst, fun Λ' hΛ' => ?_⟩
  have heq := hΛ.eqOn hΛ'
  rwa [min_self] at heq

/-- **Corrected Lemma 2.5 from the inputs** (printed proof, lines 562-584): the family of the rescaled measure exists a.s.
by Lemma 2.4 transported through the law of the rescaled circle average process (`QuantumConeScalingInput`); its inverse
rescaling is the family of Lemma 2.5 (`rescaledFamily_transfer`); uniqueness on `(0, bT^b)` is `eqOn`. The stopped family
is chosen pointwise (`Classical.epsilon`): only existence and fixed-domain uniqueness are asserted. -/
theorem coneScaleInvarianceUpToFixedTimeCorrected_of_inputs (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hG : FrozenConeHalfBallFamilyMeasurable)
    (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0})
    (h0 : FrozenWholePlaneLogLQGExistence) (h3 : FrozenConeRestriction)
    (h4 : FrozenConeHarmonicBallLocality) : ConeScaleInvarianceUpToFixedTimeCorrectedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone b hb
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨G, hGnull, hchar⟩ := hG γ hγ0 hγ2
  have hwp := wholePlaneHalfBallFamilyStep_of_hb h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58
  have hex := ae_hasConeHarmonicBallsUpToHalfBall_of_wholePlane h0 hwp h3 h4 hγ0 hγ2 hcone
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  -- the circle average process of `h` lies in `G` a.s. (Lemma 2.4)
  have hGc : ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ G := by
    filter_upwards [hex, hcont, hcone.2.2] with ω hω hc hl
    obtain ⟨T, hT, Λ, hΛ, hst⟩ := hω
    exact (hchar _ hc _ hl).2 ⟨T, Λ, hT, hΛ, hst⟩
  -- the rescaled circle average process lies in `G` a.s. (equality in law)
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) ∈ G :=
    ae_mem_of_map_eq hmeasc (coneRescaledCircleAEMeasurableStep_of_input hscale γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb)
      (hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb) (hGnull Ω P hC hcirc μ hcone) hGc
  have hlqg := coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale) γ hγ0 hγ2 Ω P hC hcirc μ
    hcone b hb
  -- a stopped family for the rescaled measure, a.s.
  have hex' : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ), 0 < y.1 ∧
      IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) y.2 y.1 ∧
      IsStoppedAtHalfBall y.2 y.1 := by
    filter_upwards [hGb, hcont, hlqg] with ω hω hc hs
    obtain ⟨T', Λ', h'⟩ := (hchar _ (continuousOn_rescaledCircle (γ := γ) hc hs.1) _ hs.2).1 hω
    exact ⟨(T', Λ'), h'⟩
  let x : Ω → ℝ × (ℝ → Set ℂ) := fun ω => Classical.epsilon fun y : ℝ × (ℝ → Set ℂ) =>
    0 < y.1 ∧ IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) y.2 y.1 ∧
      IsStoppedAtHalfBall y.2 y.1
  have hx : ∀ᵐ ω ∂P, 0 < (x ω).1 ∧
      IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (x ω).2 (x ω).1 ∧
      IsStoppedAtHalfBall (x ω).2 (x ω).1 := by
    filter_upwards [hex'] with ω hω
    exact Classical.epsilon_spec hω
  refine ⟨fun ω => (x ω).1, fun ω => rescaledFamily (x ω).2 (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹, ?_⟩
  filter_upwards [hx, hlqg] with ω hω hlq
  obtain ⟨hT, hfam, hst⟩ := hω
  exact ⟨hT, rescaledFamily_transfer hlq.1 hb hfam hst⟩

/-- **Corrected Lemma 2.4** (first-pass theorem `firstPass_2_4_corrected`). Hypotheses: the Draft statements of the
Harmonic-Balls results cited for Lemma 2.4 (HB22 Theorems 1.1, 5.5, Lemma 3.2 with their listed inputs) and the frozen
EXTERNAL inputs `FrozenWholePlaneLogLQGExistence`, `FrozenConeRestriction`, `FrozenConeHarmonicBallLocality`. -/
theorem firstPass_2_4_corrected
    (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0})
    (h0 : FrozenWholePlaneLogLQGExistence) (h3 : FrozenConeRestriction)
    (h4 : FrozenConeHarmonicBallLocality) : ConeHarmonicBallsUpToFixedTimeCorrectedStmt :=
  coneHarmonicBallsUpToFixedTimeCorrected_of_inputs h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58 h0 h3 h4

/-- **Corrected Lemma 2.5** (first-pass theorem `firstPass_2_5_corrected`). Hypotheses: `QuantumConeScalingInput` (DMS14
Proposition 4.13(i), scale invariance of the cone), `LQGMeasurePropertiesStmt` (Fact 2.2), the frozen measurability
`FrozenConeHalfBallFamilyMeasurable` (HB22 Proposition 1.3), the Harmonic-Balls Draft statements and the frozen inputs of
Lemma 2.4. -/
theorem firstPass_2_5_corrected (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hG : FrozenConeHalfBallFamilyMeasurable)
    (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0})
    (h0 : FrozenWholePlaneLogLQGExistence) (h3 : FrozenConeRestriction)
    (h4 : FrozenConeHarmonicBallLocality) : ConeScaleInvarianceUpToFixedTimeCorrectedStmt :=
  coneScaleInvarianceUpToFixedTimeCorrected_of_inputs hscale h22 hG h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58 h0 h3
    h4

end MatedCRT
