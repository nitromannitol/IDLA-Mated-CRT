import MatedCRT.FirstPass.Derived.GMS21GammaConeAnnulusTransfer
import MatedCRT.FirstPass.Derived.CanonicalReferenceEnvironmentsOfCoupling
import MatedCRT.FirstPass.Derived.ZeroConeClockedCellCode
import MatedCRT.Assembly.Canonical
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.ConeSampleMeasurable

/-!
# The premise `tutteLP` at the canonical model from the zero cone (proof of Theorem 3.4, case 1)

Gwynne–Miller–Sheffield (arXiv:1705.11161), proof of Theorem 3.4, case 1: the uniform-start invariance principle for
the `γ`-quantum cone follows from Lemma 3.5 (the invariance principle for the `0`-quantum cone with an independent
uniform phase) and local absolute continuity (Lemma 3.3). Every valid environment comes with a mating-of-trees
coupling on its own probability space (`MatedCRTEnv.IsValid.matingOfTrees`), whose `γ`-cone curve is a version of the
curve of the environment and whose boundary-length pair gives the edge multiplicities of the environment. Its
zero-cone curve and a measurable version of the boundary-length pair of the zero-cone curve
(`exists_zeroCone_clocked_shiftedCellCode`, with the measurability of the cone field from
`MatedCRTHarmonic.Canon.aemeasurable_cone_field`) give the shifted zero-cone configuration on the same space.

Hence the premise `tutteLP` of `CanonicalHypotheses ν` holds as soon as the mating-of-trees couplings exist, the form
on annuli of Lemma 3.5 (`ZeroConeAnnulusLPForm`) holds for every coupling, and Lemma 3.3 holds for every coupling in
the form `CouplingLocalConfigUMAC`: the laws of the local configurations near annuli `B_R(0) \ closedBall 0 α` of the
`γ`-cone data at mesh `1/n` and of the shifted zero-cone data at mesh `1/n` are uniformly mutually absolutely
continuous as `n → ∞`.

## Main statements

* `coneConfigData`: the `γ`-cone data at mesh `1/n` of a coupling (its curve and the contour edge counts of its
  boundary-length pair).
* `CouplingLocalConfigUMAC`: Lemma 3.3 of arXiv:1705.11161 for the local configurations of a coupling.
* `exists_isZeroConeBoundaryPair`: every coupling has a measurable version of the boundary-length pair of its zero-cone
  curve.
* `tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig`: the premise `tutteLP` of `CanonicalHypotheses ν`.
* `canonicalHypotheses_of_zeroConeAnnulusLPForm_localConfig`, `convergenceOfIDLA_canonical_of_zeroCone`,
  `convergenceOfDivSandpile_canonical_of_zeroCone`: `CanonicalHypotheses ν` and Theorems 1.4 and 1.6 at the canonical
  model from the couplings, the two forms above and the chart forms `BG20ChartFieldInput`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-- The `γ`-cone data at mesh `1/n` of a mating-of-trees coupling at `ω`: the curve `η ω` parametrized by `γ`-LQG
area and the contour edge counts at mesh `1/n` of the boundary-length pair `bm ω` (Definition 1.1). -/
def coneConfigData {Ω : Type} (η : Ω → C(ℝ, ℂ)) (bm : Ω → Path2) (n : ℕ) (ω : Ω) :
    C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (η ω, bmEdgeCount (1 / (n : ℝ)) (fun t => (bm ω t).1) (fun t => (bm ω t).2))

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield (arXiv:1705.11161) for the local configurations of a mating-of-trees
coupling.** For every measurable version `G` of the boundary-length pair of the zero-cone curve and all
`0 < α < R`, the laws under `P` of the local configurations near `B_R(0) \ closedBall 0 α` of the `γ`-cone data at
mesh `1/n` (`coneConfigData`) and the laws under `P ⊗ Unif[0, 1]` of the local configurations near the same annulus
of the zero-cone data read on the shifted lattice `n⁻¹ ℤ + n⁻¹ θ` (`zeroConeShiftedData`) are uniformly mutually
absolutely continuous as `n → ∞` (Definition 3.2 there). In the proof of Theorem 3.4, case 1, this follows from
Lemma 3.3 and the local absolute continuity of the `γ`-quantum cone and the `0`-quantum cone away from the origin
([MS16c, Proposition 3.4]). -/
def CouplingLocalConfigUMAC (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    LocalConfigUniformlyMutuallyAbsolutelyContinuous P (coneConfigData η bm) (P.prod zeroConePhase)
      (zeroConeShiftedData η₀ G)

/-- **The boundary-length pair of the zero-cone curve has a measurable version**: for every mating-of-trees coupling
there is a measurable `G` with `G ω t = bm ω (ψ t)` almost surely, `ψ` the clock of the zero cone. -/
theorem exists_isZeroConeBoundaryPair (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : ∃ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G := by
  have hQ : zeroConePhase ≪ volume := by
    unfold zeroConePhase
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hphase : ∀ᵐ θ ∂zeroConePhase, θ ∈ Icc (0 : ℝ) 1 := by
    unfold zeroConePhase
    exact ae_restrict_mem measurableSet_Icc
  obtain ⟨G, hGm, hclock, -⟩ := exists_zeroCone_clocked_shiftedCellCode D hγ
    (MatedCRTHarmonic.Canon.aemeasurable_cone_field D hγ) one_pos zeroConePhase hQ hphase
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hclock] with ω hω t
  obtain ⟨ψ, -, -, hGψ, hψ, -⟩ := hω
  rw [hGψ t, hψ t]

end Coupling

/-- **The premise `tutteLP` at the canonical model** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of
Theorem 3.4, case 1). If for every `γ ∈ (0, 2)` some mating-of-trees coupling on `ℝ` has a Lebesgue-parametrized
curve with code law `ν (16/γ²)`, and every mating-of-trees coupling on `ℝ` satisfies the form on annuli of Lemma 3.5
for its shifted zero-cone configuration (`ZeroConeAnnulusLPForm`) and Lemma 3.3 for its local configurations
(`CouplingLocalConfigUMAC`), then for every `γ ∈ (0, 2)` the canonical model `ProbeMi.canonicalSLEModel ν` has a valid
environment, with a measurable version of its curve, whose walk and Brownian motion stopped at their exits from
`B_R(0)` are close in Lévy–Prokhorov distance from every selected start with probability tending to one: the field
`tutteLP` of `CanonicalHypotheses ν`. -/
theorem tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hZ : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConeAnnulusLPForm D hγ)
    (h33 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), CouplingLocalConfigUMAC D hγ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ := by
  intro γ hγ0 hγ2
  have hγI : γ ∈ Ioo (0 : ℝ) 2 := ⟨hγ0, hγ2⟩
  obtain ⟨S₀, hS₀⟩ :=
    FirstPass.Derived.hasReferenceEnvironments_canonicalSLEModel_of_coupling ν hcpl γ hγ0 hγ2
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, D, hae⟩ := hS₀.matingOfTrees
  have hη' : ∀ᵐ ω ∂S₀.P, ⇑(η' ω) = S₀.η ω := hae.mono fun ω h => h.1
  have hη'm : Measurable η' := D.measurable_curves.2.1
  obtain ⟨G, hG⟩ := exists_isZeroConeBoundaryPair D hγI
  refine ⟨ProbeMi.canonicalSLEModel ν, FirstPass.Derived.hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl,
    ℝ, inferInstance, S₀, hS₀, η', hη'm, hη', ?_⟩
  exact tendsto_uniformStartSelectedLPData_of_zeroConeAnnulusLPForm hγ0 hγ2 hS₀ hη'm hη' D hγI hG
    (hZ γ hγI D) (h33 γ hγI D G hG)

/-- **`CanonicalHypotheses ν` from the couplings, the zero cone and the chart forms.** The premise `tutteLP` is
`tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig`. -/
theorem canonicalHypotheses_of_zeroConeAnnulusLPForm_localConfig (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hZ : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConeAnnulusLPForm D hγ)
    (h33 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), CouplingLocalConfigUMAC D hγ)
    (hchart : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    CanonicalHypotheses ν :=
  ⟨hcpl, tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig ν hcpl hZ h33, hchart⟩

/-- **Theorem 1.4** (convergence of IDLA) at the canonical model from the couplings, the form on annuli of Lemma 3.5
for the zero cone, Lemma 3.3 and the chart forms of Berestycki–Gwynne. -/
theorem convergenceOfIDLA_canonical_of_zeroCone (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hZ : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConeAnnulusLPForm D hγ)
    (h33 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), CouplingLocalConfigUMAC D hγ)
    (hchart : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  convergenceOfIDLA_canonical ν (canonicalHypotheses_of_zeroConeAnnulusLPForm_localConfig ν hcpl hZ h33 hchart)

/-- **Theorem 1.6** (convergence of the divisible sandpile) at the canonical model from the couplings, the form on
annuli of Lemma 3.5 for the zero cone, Lemma 3.3 and the chart forms of Berestycki–Gwynne. -/
theorem convergenceOfDivSandpile_canonical_of_zeroCone (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hZ : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConeAnnulusLPForm D hγ)
    (h33 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), CouplingLocalConfigUMAC D hγ)
    (hchart : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  convergenceOfDivSandpile_canonical ν
    (canonicalHypotheses_of_zeroConeAnnulusLPForm_localConfig ν hcpl hZ h33 hchart)

end MatedCRT
