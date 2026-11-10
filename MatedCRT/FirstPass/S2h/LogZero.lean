import MatedCRT.FirstPass.S2g.Transfer
import MatedCRT.FirstPass.S2h.CertCode
import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.FirstPass.Frozen.S2g
import HarmonicBalls.Draft.Section3

/-!
# Zero law of the certificate code for the log-GFF (fp-S2h, z1, round 10)

Reduction of the log-GFF zero law `LogCertCodeNullStep` (`FirstPass/S2h.lean`) to the fixed-radius zero law
`HalfPlateauNullStep` at radius `1/2` (CHATGPT-cone-good-set.md Sections 5.1-5.4, referee CORRECT). The measure theory:
the analytic code set is universally measurable (`FrozenUniversalMeasurabilityOfAnalytic`); the certificate iff
(`CertCodeExactStep`) and the transfer `half_mem_plateauRadii_of_hasRatPlateauCert` (S2g/Transfer.lean:82) identify the
code event with the plateau event at radius `1/2`; the almost sure cluster compatibility `ClusterCompatibilityStmt`
(HB Lemma 3.5, Draft Section 3) supplies the pathwise hypothesis of the transfer.
The code map must be almost everywhere measurable (`hYm`): Mathlib's `Measure.map` of a non-AE-measurable map is a Dirac
mass, not zero, so the law statement needs it (fidelity point, see the report).
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- Pathwise good event of a measure for the transfer to radius `1/2`: local finiteness and the compatibility of the
clusters in `B_{3/4}` and `B_1` at every positive time (HB Lemma 3.5 in the form of `ClusterCompatibilityStmt` with
`s₁ = s₂ = 3/4`, `R = 1`, pole `0`). -/
def PathwiseGoodPlateau (ν : Measure ℂ) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ∀ t : ℝ, 0 < t → ∀ s ∈ Icc (3 / 4 : ℝ) 1,
    closure (cluster ν (3 / 4) 0 t) ⊆ ball 0 (3 / 4) → cluster ν s 0 t = cluster ν (3 / 4) 0 t

/-- **OPEN (NEW; z1, round 10).** Zero law at the fixed radius `1/2` for the log-GFF: for every whole-plane log field
`h^ℂ − γ log|·|` (`IsWholePlaneGFF`, `IsLQGMeasureOfField P γ γ`), the (outer) probability that the plateau radii of the
LQG measure contain `1/2` is zero. Written argument: CHATGPT-cone-good-set.md Section 5 (5.1 Borel versions of the
positivity coordinates with one common null set; 5.2 countable sections and Tonelli (37)-(39); 5.3 scaling (40)-(45)).
Its measure-level scaling input is not yet frozen. Not proved. -/
def HalfPlateauNullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → P {ω | (1 / 2 : ℝ) ∈ plateauRadii (μ ω)} = 0

/-- Reduction (fp-S2h, round 10): the log-GFF zero law for an exact code pair (the statement `LogCertCodeNullStep`) follows
from the fixed-radius zero law `HalfPlateauNullStep`, the analytic code set and its certificate iff, the transfer
`half_mem_plateauRadii_of_hasRatPlateauCert`, the cited cluster compatibility `ClusterCompatibilityStmt`, and the
almost everywhere measurability `hYm` of the code map. -/
theorem logCertCodeNull_of_half (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hcomp : ClusterCompatibilityStmt.{0}) (hhalf : HalfPlateauNullStep)
    (φs : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)) (hB : AnalyticSet B)
    (hiff : ∀ ν : Measure ℂ, (∀ n : ℕ, ν (closedBall (0 : ℂ) n) < ⊤) →
      (HasRatPlateauCert ν ↔ localCode φs ν ∈ B))
    (hYm : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ γ hcirc μ → AEMeasurable (fun ω => localCode φs (μ ω)) P) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ γ hcirc μ → (P.map fun ω => localCode φs (μ ω)) B = 0 := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hP hgff hlgm
  have hY : AEMeasurable (fun ω => localCode φs (μ ω)) P := hYm γ hγ hγ2 Ω P hC hcirc μ hP hgff hlgm
  have hBn : NullMeasurableSet B (P.map fun ω => localCode φs (μ ω)) :=
    hF1 (ℕ → ℝ) (P.map fun ω => localCode φs (μ ω)) (by infer_instance) B hB
  rw [Measure.map_apply₀ hY hBn]
  have hγne : γ ≠ 0 := hγ.ne'
  have hlt : γ < lqgQ γ := by
    unfold lqgQ
    have h4 : γ * γ < 4 := by nlinarith
    have key : 2 / γ - γ / 2 = (4 - γ * γ) / (2 * γ) := by
      field_simp
      ring
    have hpos : 0 < (4 - γ * γ) / (2 * γ) := div_pos (by linarith) (by linarith)
    linarith
  have hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    Filter.Eventually.mono hlgm fun ω hω => hω.isLocallyFiniteMeasure
  have hcompA : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ s ∈ Icc (3 / 4 : ℝ) 1,
      closure (cluster (μ ω) (3 / 4) 0 t) ⊆ ball 0 (3 / 4) → cluster (μ ω) s 0 t = cluster (μ ω) (3 / 4) 0 t := by
    filter_upwards [hcomp γ γ hγ hγ2 hlt Ω P hC hcirc μ hgff hlgm 1 one_pos] with ω hω
    intro t ht s hs hcl
    exact hω t ht (3 / 4) (by norm_num) 0 (mem_ball_self (by norm_num)) (3 / 4) ⟨le_refl _, by norm_num⟩ hcl s hs
  have hgood : ∀ᵐ ω ∂P, PathwiseGoodPlateau (μ ω) := by
    filter_upwards [hlf, hcompA] with ω h1 h2
    exact ⟨h1, h2⟩
  have hbad : P {ω | ¬ PathwiseGoodPlateau (μ ω)} = 0 := ae_iff.mp hgood
  have hsub : (fun ω => localCode φs (μ ω)) ⁻¹' B ⊆
      {ω | (1 / 2 : ℝ) ∈ plateauRadii (μ ω)} ∪ {ω | ¬ PathwiseGoodPlateau (μ ω)} := by
    intro ω hω
    by_cases hg : PathwiseGoodPlateau (μ ω)
    · left
      obtain ⟨hloc, hc⟩ := hg
      have := hloc
      have hfin : ∀ n : ℕ, μ ω (closedBall (0 : ℂ) n) < ⊤ := fun n => measure_closedBall_lt_top
      have hcert : HasRatPlateauCert (μ ω) := (hiff (μ ω) hfin).2 hω
      exact half_mem_plateauRadii_of_hasRatPlateauCert hmin hpole measure_closedBall_lt_top hc hcert
    · exact Or.inr hg
  refine le_antisymm (le_trans (measure_mono hsub) ?_) zero_le
  refine le_trans (measure_union_le _ _) (le_of_eq ?_)
  rw [hhalf γ hγ hγ2 Ω P hC hcirc μ hP hgff hlgm, hbad, add_zero]

end MatedCRT
