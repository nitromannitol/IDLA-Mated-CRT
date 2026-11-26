import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLP
import MatedCRT.FirstPass.Derived.GMS21Lemma33Cone
import MatedCRT.FirstPass.Derived.ConeAreaBumpTiltProof
import MatedCRT.FirstPass.Derived.GMSSmallCellEstimateProof
import MatedCRT.FirstPass.Derived.ZeroConeLemma35StepsProof
import MatedCRT.FirstPass.Derived.ZeroConeEdgeCountCodeProof

/-!
# The premise `tutteLP` at the canonical model from Theorem 3.10 and the quenched unit-scale convergence

Gwynne–Miller–Sheffield (arXiv:1705.11161), proof of Theorem 3.4, case 1, with Lemma 3.5 proved through the quenched
unit-scale convergence of the zero-cone cells (proof of Lemma 3.5, lines 1327-1343). The form on annuli of Lemma 3.5
for the shifted zero-cone configuration (`ZeroConeAnnulusLPForm`) follows from

* the quenched convergence of the unit-scale errors (`ZeroConeQuenchedUnitScaleConvergence`), which Theorem 3.10 of
  arXiv:1807.07515 (`GMSTheorem310`) gives on the law of a polygonal cell configuration carrying the zero-cone walk
  (`ZeroConePolygonalConfiguration`), with the small-cell estimate of Lemmas 2.8-2.9 there (`gmsSmallCellEstimate`);
* the scaling law of the weighted cell data (`ZeroConeWeightedMeshScaling`), from the dilation law of the zero-cone
  curve (`zeroConeCurveDilationLaw`) and the dilation-invariant code of the edge counts (`ZeroConeEdgeCountCode`);
* the measurability of the uniform errors (`ZeroConeWeightedUniformErrorMeasurability`), from the Borel projection
  form of their superlevel events (`weightedErrorSuperlevelBorelProjection`);
* the measurability of the cone field (`MatedCRTHarmonic.Canon.aemeasurable_cone_field`).

Lemma 3.3 for the local configurations (`CouplingLocalConfigUMAC`) follows from its three inputs, of which the offset
density `ConeOffsetDensity` is proved (`coneOffsetDensity_of_bumpTilt`, `coneAreaBumpTilt`). Together with the
couplings they give the premise `tutteLP` of `CanonicalHypotheses` at the canonical model.

## Main statements

* `tutteLP_canonical_of_theorem310_quenchedZeroCone_edgeCountCode`: the premise `tutteLP` at the canonical model, with
  the code of the edge counts as a premise.
* `tutteLP_canonical_of_theorem310_quenchedZeroCone`: the same, with the code of the edge counts from its two inputs on
  correlated Brownian motion (`zeroConeEdgeCountCode`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b GMS310Transfer

/-- **The premise `tutteLP` at the canonical model from Theorem 3.10, the polygonal configuration and the code of
the edge counts** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1, and proof of Lemma 3.5).
If the couplings with code law `ν (16/γ²)` exist, Theorem 3.10 of arXiv:1807.07515 holds, every mating-of-trees
coupling on `ℝ` has a polygonal cell configuration carrying the walk of its zero-cone cells and a dilation-invariant
code of the edge counts of its zero-cone cells, and the first and third inputs of Lemma 3.3 hold for every
`γ ∈ (0, 2)`, then for every `γ ∈ (0, 2)` the canonical model has a valid environment whose walk and Brownian motion
stopped at their exits from `B_R(0)` are close in Lévy–Prokhorov distance from every selected start with probability
tending to one. -/
theorem tutteLP_canonical_of_theorem310_quenchedZeroCone_edgeCountCode (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (h310 : GMSTheorem310)
    (hpoly : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConePolygonalConfiguration D hγ)
    (hcode : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConeEdgeCountCode D hγ)
    (h1 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeAnnulusAreaLawEquivalence γ)
    (h3 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeConfigReconstruction γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ :=
  tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig ν hcpl
    (fun γ hγ P X _ _ B B' _ _ _ _ _ _ _ D => by
      have hf : AEMeasurable (fun ω => coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P :=
        MatedCRTHarmonic.Canon.aemeasurable_cone_field D hγ
      exact zeroConeAnnulusLPForm_of_quenchedUnitScaleConvergence D hγ hf
        (zeroConeQuenchedUnitScaleConvergence_of_polygonal D hγ hf h310 gmsSmallCellEstimate (hpoly γ hγ D))
        (zeroConeWeightedMeshScaling_of_curveDilationLaw D hγ (zeroConeCurveDilationLaw D hγ) (hcode γ hγ D))
        (zeroConeWeightedUniformErrorMeasurability_of_superlevelProjection D hγ
          weightedErrorSuperlevelBorelProjection))
    (fun γ hγ _ _ _ _ _ _ _ _ _ _ _ _ _ D => forall_couplingLocalConfigUMAC_of_lemma33Inputs h1
      (fun γ' _ => coneOffsetDensity_of_bumpTilt γ' (coneAreaBumpTilt γ')) h3 γ hγ D)

/-- **The premise `tutteLP` at the canonical model from Theorem 3.10 and the quenched unit-scale convergence**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1, and proof of Lemma 3.5). If the couplings
with code law `ν (16/γ²)` exist, Theorem 3.10 of arXiv:1807.07515 holds, every mating-of-trees coupling on `ℝ` has a
polygonal cell configuration carrying the walk of its zero-cone cells, two correlated Brownian coordinates have no
common local minimum time (`CorrelatedBMNoCommonLocalMin`), the points visited three times by a Peanosphere curve of
a correlated Brownian motion contain no continuum (`CorrelatedBMPeanosphereTriplePointsNoContinuum`), and the first
and third inputs of Lemma 3.3 hold for every `γ ∈ (0, 2)`, then for every `γ ∈ (0, 2)` the canonical model has a valid
environment whose walk and Brownian motion stopped at their exits from `B_R(0)` are close in Lévy–Prokhorov distance
from every selected start with probability tending to one. -/
theorem tutteLP_canonical_of_theorem310_quenchedZeroCone (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (h310 : GMSTheorem310)
    (hpoly : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConePolygonalConfiguration D hγ)
    (hcone : CorrelatedBMNoCommonLocalMin) (htriple : CorrelatedBMPeanosphereTriplePointsNoContinuum)
    (h1 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeAnnulusAreaLawEquivalence γ)
    (h3 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeConfigReconstruction γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ :=
  tutteLP_canonical_of_theorem310_quenchedZeroCone_edgeCountCode ν hcpl h310 hpoly
    (fun _ hγ _ _ _ _ _ _ _ _ _ _ _ _ _ D => zeroConeEdgeCountCode hcone htriple D hγ) h1 h3

end MatedCRT
