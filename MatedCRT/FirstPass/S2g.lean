import MatedCRT.FirstPass.S2e
import MatedCRT.Proofs.Sec2.ConeFamily

/-! # First pass, wave 7: Lemmas 2.4 and 2.5 in their canonical form (q1, fp-S2g)

Statements (corrected, canonical stopping time): `notes/fp-gaps/CHATGPT-2-4-2-5-statements.md`, checked FAITHFUL in
`notes/fp-gaps/CHATGPT-2-4-2-5-fidelity.md` (operator, 2026-11-09 19:45 and 20:25).

* `halfBallTime μ = sup {t > 0 : regularizedCluster μ (3/4) 0 t ⊆ B_{1/2}}`: the printed maximal containment time
  `T = sup {t > 0 : Λ_t ⊂ B_{1/2}}` (paper lines 533-537), read through the local obstacle continuation in `B_{3/4}`.
* `UniqueConeFamilyOn μ Λ T`: `Λ` is a family of harmonic balls on `(0, T)` with the properties of Theorem 2.3, and every
  such family on the same interval `(0, T)` agrees with `Λ` there. No equality of competing stopping times, no strict growth.
* `IsStoppedAtHalfBall` is kept only as a consequence at the canonical `T`; it does not define maximality.
* Lemma 2.5 joint law: `P.map J = P.map Jb` for the cone process `J` of `Λ` and the rescaled process `Jb` of `Λb`.

This file lands the statements and proves the deterministic and conditional parts. The pathwise existence of the canonical
family is the OPEN step `ConeCanonicalHalfBallStep` (not frozen, not proved). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The canonical half-ball time of a measure on `ℂ`: the supremum of the times `t > 0` at which the regularized
cluster of the local obstacle problem in `B_{3/4}` (centre `0`) lies in `B_{1/2}` (paper lines 533-537, canonical `T`). -/
noncomputable def halfBallTime (μ : Measure ℂ) : ℝ :=
  sSup {t : ℝ | 0 < t ∧ HarmonicBalls.regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)}

/-- `Λ` is the unique family of harmonic balls on `(0, T)` in the sense of Lemma 2.4: it has the properties of
Theorem 2.3 on `(0, T)`, and every family with the same properties on `(0, T)` agrees with it there. -/
def UniqueConeFamilyOn (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  IsConeHarmonicBallFamilyOn μ Λ T ∧ ∀ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn μ Λ' T → EqOn Λ' Λ (Ioo 0 T)

/-- **Corrected Lemma 2.4, canonical form** (`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`). For `0 < γ < 2` and a cone
field, `T = halfBallTime (μ ω)` is measurable, there is a random family `Λ` whose joint process with the circle process is
measurable, and almost surely `T > 0`, `Λ` is unique on `(0, T)` and stopped at `∂B_{1/2}` at `T`. -/
def ConeHarmonicBallsUpToFixedTimeCanonicalStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    AEMeasurable (fun ω => halfBallTime (μ ω)) P ∧ ∃ Λ : Ω → ℝ → Set ℂ,
      AEMeasurable (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (halfBallTime (μ ω)))) P ∧
      ∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ UniqueConeFamilyOn (μ ω) (Λ ω) (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall (Λ ω) (halfBallTime (μ ω))

/-- **Corrected Lemma 2.5, canonical form** (`ConeScaleInvarianceUpToFixedTimeCanonicalStmt`). For a cone field, a stopped
family `Λ` for `μ` at the canonical time, and `b > 0`: with `R = R_b` the cone scale radius, `ν = b⁻¹ μ(R ·)` and
`Tb = halfBallTime ν`, the time `Tb` is measurable, there is `Λb` with `Λb` unique on `(0, b Tb)` and its rescaling stopped
at `∂B_{1/2}` at `Tb`, and the joint laws of the circle process with the family agree:
`P.map J = P.map Jb`. -/
def ConeScaleInvarianceUpToFixedTimeCanonicalStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ Λ : Ω → ℝ → Set ℂ,
      (∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall (Λ ω) (halfBallTime (μ ω))) →
    ∀ b : ℝ, 0 < b →
      let R := fun ω => coneScaleRadius γ (hcirc ω) b
      let ν := fun ω => ENNReal.ofReal (b⁻¹) • (μ ω).map (fun z : ℂ => z / (R ω : ℂ))
      let Tb := fun ω => halfBallTime (ν ω)
      AEMeasurable Tb P ∧ ∃ Λb : Ω → ℝ → Set ℂ,
        (∀ᵐ ω ∂P, 0 < Tb ω ∧ UniqueConeFamilyOn (μ ω) (Λb ω) (b * Tb ω) ∧
          IsStoppedAtHalfBall (rescaledFamily (Λb ω) (R ω) b) (Tb ω)) ∧
        let J := fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (halfBallTime (μ ω)))
        let Jb := fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b),
          familyProcess (rescaledFamily (Λb ω) (R ω) b) (Tb ω))
        AEMeasurable J P ∧ AEMeasurable Jb P ∧ P.map J = P.map Jb

/-- **Uniqueness on the fixed interval** (deterministic). A cone family on `(0, T)` is unique there: any other cone family
on `(0, T)` agrees with it on `(0, T)`, by the fixed-time uniqueness `IsConeHarmonicBallFamilyOn.eqOn`. -/
theorem uniqueConeFamilyOn_of_family {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (h : IsConeHarmonicBallFamilyOn μ Λ T) : UniqueConeFamilyOn μ Λ T := by
  refine ⟨h, fun Λ' hΛ' => ?_⟩
  have heq := h.eqOn hΛ'
  rwa [min_self] at heq

/-- **OPEN NEW step (q1, fp-S2g; neither proved nor frozen).** Pathwise canonical stopped family: almost surely the
half-ball time `halfBallTime (μ ω)` is positive and some family of harmonic balls on `(0, halfBallTime (μ ω))` is stopped
at `∂B_{1/2}` at that time. This is the existence half of Lemma 2.4 at the canonical `T`. Its replacement for the retired
`FrozenConeHarmonicBallLocality` is the measurable good event of `notes/fp-gaps/G-S2-measurable.md` Section 3 (local
obstacle locality in `B_{3/4}`, Hausdorff continuity of the closed clusters, and the first-exit identity at `T`). -/
def ConeCanonicalHalfBallStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ∃ Λ : ℝ → Set ℂ, 0 < halfBallTime (μ ω) ∧
      IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧ IsStoppedAtHalfBall Λ (halfBallTime (μ ω))

/-- **Corrected Lemma 2.4, canonical form, from the pathwise canonical family and the closure step (q1, fp-S2g).**
Measurability of the canonical time and of the joint process follows from `ConeHalfBallClosureInsideStep` (closure
containment of the stopped families, `FirstPass/S2d.lean`) through `S2e`; uniqueness on `(0, T)` is deterministic. -/
theorem firstPass_2_4_canonical_of_steps (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  have hex := hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone
  have hcl' := hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone
  let x : Ω → ℝ → Set ℂ := fun ω => Classical.epsilon fun Λ : ℝ → Set ℂ =>
    0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall Λ (halfBallTime (μ ω))
  have hx : ∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) (x ω) (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall (x ω) (halfBallTime (μ ω)) := by
    filter_upwards [hex] with ω hω
    exact Classical.epsilon_spec hω
  have hT := aemeasurable_coneHalfBallStoppingTime_closureInside hγ0 hγ2 hcone h27 hcl'
    (T := fun ω => halfBallTime (μ ω)) (Λ := x) hx
  have hJ := aemeasurable_coneHalfBallPair_closureInside hγ0 hγ2 hcone h27 hcl'
    (T := fun ω => halfBallTime (μ ω)) (Λ := x) hx
  refine ⟨hT, x, hJ, ?_⟩
  filter_upwards [hx] with ω hω
  exact ⟨hω.1, uniqueConeFamilyOn_of_family hω.2.1, hω.2.2⟩

end MatedCRT
