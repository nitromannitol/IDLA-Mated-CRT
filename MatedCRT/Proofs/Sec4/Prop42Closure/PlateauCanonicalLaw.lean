import MatedCRT.Proofs.Sec4.Prop42Closure.GlobalRadiusMeasurable
import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScaleLaw
import HarmonicBalls.Steps.Sec3.Basic

/-! # Conditional closure of `PlateauScaleInvarianceStep` on the canonical plateau event (Proposition 4.2)

The
scaling of lines 245-256 (inputs K and H, `PlateauScaleLaw.lean`) and the probability identity of line 265, whose
measurability is the canonical event of lines 263-268 (`GlobalRadiusMeasurable.lean`).

`plateauScaleInvarianceStep_of_canonical` proves `PlateauScaleInvarianceStep` (`HalfBallPlateau.lean:51`) from three
hypotheses, each a `Prop` in full with its source:
* `LQGVolumeGrowthAllScalesStmt.{0}` (input I2 of Harmonic-Balls-LQG, `HarmonicBalls/Draft/Section2.lean:122`): almost
  surely every whole-plane LQG measure has volume growth on every ball `B_R`. This is an existing explicit
  Harmonic-Balls input, not a new literature statement and not a proved volume-growth theorem. It is applied to `μ` and to
  the scaled measure `μ''` of input K, each from its own whole-plane GFF/LQG data, by
  `ae_isLocallyFiniteMeasure_volumeGrowth` (`HarmonicBalls/Steps/Sec3/Basic.lean:71`).
* `InsertionLQGScalingLawStep` (input K) and `ScaledRegularizedFamilyStep` (input H), from `PlateauScaleLaw.lean`.

The former global input `GlobalPlateauMeasurableStep` (measurability of the plateau predicate on all measures) is not
assumed. The law transfer is `plateau_prob_eq_canonical` (`GlobalRadiusMeasurable.lean:222`), which needs only the canonical
measurable plateau event `plateau_event_ae_eq_canonical`. No separate `AEMeasurable μ` hypothesis is needed: the identity
`IdentDistrib μ'' μ P P` supplied by input K contains the measurability of both measures. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls ProbabilityTheory
open scoped Pointwise ENNReal

/-- **`PlateauScaleInvarianceStep`, conditional on inputs I2, K and H.** For `a, r > 0`, the probability that `r` is a
plateau value equals the probability that `a r` is one (draft line 265, `p(r) = p(ar)`).

The proof. Input K gives the scaled measure `μ'' = scaledMeasure μ a c` with `μ'' =_d μ` (`scaledMeasure_eq_of_map`), and
input H makes the dilated family regularized for `μ''`. Input I2, applied to `μ` and to `μ''`, gives the volume growth on
every disk `B_(n+1)` that `plateau_prob_eq_canonical` needs. That lemma equates `P[r ∈ P(Λ)]` and `P[r ∈ P(Λ_a)]`. The
pathwise identity `r ∈ P(Λ_a) ↔ a r ∈ P(Λ)` (time change, `mem_plateauValues_scaledFamily_iff`) gives the claim. -/
theorem plateauScaleInvarianceStep_of_canonical (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : InsertionLQGScalingLawStep) (hH : ScaledRegularizedFamilyStep) : PlateauScaleInvarianceStep := by
  intro γ α hγ hγ2 hα Ω _ P hC hcirc μ Λ hP hWP hLQG hreg a r ha hr
  obtain ⟨hC'', hcirc'', μ'', c, hWP'', hLQG'', hcoord, hid⟩ :=
    hK γ α hγ hγ2 hα Ω P hC hcirc μ hP hWP hLQG a ha
  have hμ : ∀ᵐ ω ∂P, μ'' ω = scaledMeasure (μ ω) a (c ω) := by
    filter_upwards [hcoord] with ω hω
    exact (scaledMeasure_eq_of_map hω.1 hω.2).symm
  have hreg' : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ'' ω) (scaledFamily (Λ ω) a (c ω)) 0 := by
    filter_upwards [hreg, hμ, hcoord] with ω h1 h2 h3
    rw [h2]
    exact hH (μ ω) (Λ ω) a (c ω) ha h3.1 h1
  -- Volume growth on every disk `B_(n+1)`, for `μ` and for `μ''`, each from its own whole-plane GFF/LQG data (input I2).
  obtain ⟨βm, βp, hvg⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP hLQG
  obtain ⟨βm', βp', hvg'⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP'' hLQG''
  have hvgN : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus : ℝ, VolumeGrowth (μ ω) ((n : ℝ) + 1) βminus βplus :=
    hvg.mono fun ω hω n => ⟨hω.1, βm, βp, hω.2 ((n : ℝ) + 1) (by positivity)⟩
  have hvgN' : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLocallyFiniteMeasure (μ'' ω) ∧
      ∃ βminus βplus : ℝ, VolumeGrowth (μ'' ω) ((n : ℝ) + 1) βminus βplus :=
    hvg'.mono fun ω hω n => ⟨hω.1, βm', βp', hω.2 ((n : ℝ) + 1) (by positivity)⟩
  obtain ⟨G, hG⟩ := exists_canonicalRawClusterFamilies
  have hmono : ∀ᵐ ω ∂P, MonotoneOn (fun t => familyRadius (Λ ω t)) (Ioi 0) := by
    filter_upwards [hreg] with ω h1
    exact familyRadius_monotoneOn_of_regularized h1
  have hpath : {ω | r ∈ plateauValues (scaledFamily (Λ ω) a (c ω))} =ᵐ[P]
      {ω | a * r ∈ plateauValues (Λ ω)} := by
    filter_upwards [hcoord, hmono] with ω h3 h4
    exact propext (mem_plateauValues_scaledFamily_iff ha h3.1 h4 r)
  calc P {ω | r ∈ plateauValues (Λ ω)}
      = P {ω | r ∈ plateauValues (scaledFamily (Λ ω) a (c ω))} :=
        plateau_prob_eq_canonical hid hvgN hvgN' hreg hreg' hG r
    _ = P {ω | a * r ∈ plateauValues (Λ ω)} := measure_congr hpath

end MatedCRT
