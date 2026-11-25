import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepair
import LatticeProb.Topology.PolishContinuousMap
import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# The scaling and the measurability steps of the annulus form of Lemma 3.5 of Gwynne–Miller–Sheffield

The written answer `notes/fp-gaps/CODEX-MQ-sbl-22.md` proves the two steps `ZeroConeWeightedMeshScaling` (section A3,
lines 43 and 53) and `ZeroConeWeightedUniformErrorMeasurability` (section A4, lines 57-59) of
`GMS21ZeroConeAnnulusRepair.lean`. This file follows those sections.

* A3 (lines 43, 53). The radius `R_b`, `b = 1/n`, is a Borel function of the circle-average process of the zero-cone
  field, and the rescaled curve `η^b(t) = R_b⁻¹ η₀(b t)` has the law of `η₀` (DMS, Proposition 4.13(i); GMS (2.4)-(2.5)
  and lines 1334-1343). The rescaled unit cells at the phase `θ` are the dilates by `R_b⁻¹` of the mesh-`b` cells, and
  the integer edge counts are preserved by this dilation. These two facts are the named steps
  `ZeroConeCurveDilationLaw` and `ZeroConeEdgeCountCode`; the law identity of the weighted data is then proved
  (`zeroConeWeightedMeshScaling_of_curveDilationLaw`).
* A4 (lines 57-59). The strict superlevel events of the uniform errors are projections of Borel events of the data and
  of the parameters `(s, z, j)` (the named step `WeightedErrorSuperlevelBorelProjection`); projections of Borel subsets
  of Polish spaces are analytic, analytic sets are measurable for the completion of every finite measure (Lusin;
  Kechris, Theorem 21.10, `LatticeProb.AnalyticSet.nullMeasurableSet`), and the thresholds give an almost measurable
  function (`zeroConeWeightedUniformErrorMeasurability_of_superlevelProjection`).

## Main declarations

* `curveMeshRescale`, `weightedCurveData`: the curve read at mesh `1/n`, and the unit-mesh weighted datum of a curve
  whose edge counts are read from the curve.
* `ZeroConeCurveDilationLaw`, `ZeroConeEdgeCountCode`, `WeightedErrorSuperlevelBorelProjection`: the named steps.
* `zeroConeWeightedMeshScaling_of_curveDilationLaw`,
  `zeroConeWeightedUniformErrorMeasurability_of_superlevelProjection`: the two steps of the repair from them.
* `zeroConeAnnulusLPForm_of_theorem310_dilation`: the annulus form of Lemma 3.5 from Theorem 3.10 of arXiv:1807.07515
  and the named steps.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

/-- The curve read at mesh `1/n`: `t ↦ η(t / n)`. -/
def curveMeshRescale (n : ℕ) (q : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  q.comp ⟨fun t => t / (n : ℝ), continuous_id.div_const _⟩

/-- The **unit-mesh weighted datum of a curve** with edge counts read from the curve by `Ψ`: the curve
`t ↦ q(t + θ)` together with `Ψ` of it. -/
def weightedCurveData (Ψ : C(ℝ, ℂ) → (ℤ → ℤ → ℕ)) (q : C(ℝ, ℂ) × ℝ) : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (phaseShiftedCurve 1 q.2 q.1, Ψ (phaseShiftedCurve 1 q.2 q.1))

theorem continuous_phaseShiftedCurve_one :
    Continuous fun q : C(ℝ, ℂ) × ℝ => phaseShiftedCurve 1 q.2 q.1 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  change Continuous fun q : (C(ℝ, ℂ) × ℝ) × ℝ => q.1.1 (q.2 + 1 * q.1.2)
  fun_prop

theorem measurable_weightedCurveData {Ψ : C(ℝ, ℂ) → (ℤ → ℤ → ℕ)} (hΨ : Measurable Ψ) :
    Measurable (weightedCurveData Ψ) := by
  have h1 := continuous_phaseShiftedCurve_one.measurable
  have h2 := hΨ.comp h1
  exact h1.prodMk h2

/-- If `q(t/n) = R e(t)` for all `t`, the curve `q` read at mesh `1/n` and phase `θ` is `R` times the curve `e` read at
mesh `1` and phase `θ`. -/
theorem phaseShiftedCurve_curveMeshRescale {n : ℕ} (θ : ℝ) {q e : C(ℝ, ℂ)} {R : ℝ}
    (h : ∀ t : ℝ, q (t / (n : ℝ)) = R • e t) :
    phaseShiftedCurve 1 θ (curveMeshRescale n q) = R • phaseShiftedCurve 1 θ e := by
  ext t
  show q ((t + 1 * θ) / (n : ℝ)) = R • e (t + 1 * θ)
  exact h _

theorem curveMeshRescale_one (q : C(ℝ, ℂ)) : curveMeshRescale 1 q = q := by
  ext t
  show q (t / ((1 : ℕ) : ℝ)) = q t
  rw [Nat.cast_one, div_one]

/-- The law under `P ⊗ Unif[0, 1]` of a function of a random curve and the phase is the image of the product of the
law of the curve with the uniform phase. -/
theorem map_prod_zeroConePhase_comp {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] {Φ : C(ℝ, ℂ) × ℝ → β} (hΦ : Measurable Φ) {F : Ω → C(ℝ, ℂ)} (hF : Measurable F) :
    (P.prod zeroConePhase).map (fun p => Φ (F p.1, p.2)) = ((P.map F).prod zeroConePhase).map Φ := by
  have h1 : (P.map F).prod zeroConePhase = (P.prod zeroConePhase).map (Prod.map F id) := by
    have h := Measure.map_prod_map P zeroConePhase hF measurable_id
    rwa [Measure.map_id] at h
  rw [h1, Measure.map_map hΦ (hF.prodMap measurable_id)]
  rfl

/-- An extended nonnegative function on a Polish space whose strict superlevel sets are projections of Borel subsets
of the product with a Polish parameter space is almost measurable for every finite measure (the projections are
analytic and analytic sets are null-measurable: Lusin; Kechris, *Classical Descriptive Set Theory*, Theorem 21.10). -/
theorem aemeasurable_of_superlevel_eq_image_fst {α Z : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {f : α → ℝ≥0∞} (hf : ∀ t : ℝ≥0∞, ∃ B : Set (α × Z), MeasurableSet B ∧ {w | t < f w} = Prod.fst '' B)
    (μ : Measure α) [IsFiniteMeasure μ] : AEMeasurable f μ := by
  have hnull : ∀ t : ℝ≥0∞, NullMeasurableSet (f ⁻¹' Ioi t) μ := by
    intro t
    obtain ⟨B, hB, hBeq⟩ := hf t
    have hA : AnalyticSet (f ⁻¹' Ioi t) := by
      rw [show f ⁻¹' Ioi t = {w | t < f w} from rfl, hBeq]
      exact hB.analyticSet.image_of_continuous continuous_fst
    exact LatticeProb.AnalyticSet.nullMeasurableSet μ hA
  have hM : @Measurable (NullMeasurableSpace α μ) ℝ≥0∞ _ _ f := measurable_of_Ioi hnull
  have hNM : NullMeasurable f μ := hM
  exact hNM.aemeasurable

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The dilation law of the zero-cone curve** (written answer `notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 43: "Its
radius `R_b` is the largest positive solution of `h_{0,r}(0) + Q log r = γ⁻¹ log b` ... These hitting times are
Borel, finite and tend to infinity as `b ↓ 0` ... The scaled field `h^b = h₀(R_b ·) + Q log R_b − γ⁻¹ log b` has the
zero-cone law. Conditional on `h₀`, `R_b⁻¹ e(R_b² ·)` has the original independent curve law. Coordinate covariance
gives `μ_{h^b}(A) = b⁻¹ μ₀(R_b A)`, hence `η^b(t) = R_b⁻¹ η₀(b t)`. All these path variables admit raw measurable
versions; countably many `b = 1/n` share one event"; Gwynne–Miller–Sheffield, arXiv:1705.11161, (2.4)-(2.5) and
lines 1334-1343; Duplantier–Miller–Sheffield, arXiv:1409.7055, Proposition 4.13(i)). PENDING TRUTH CHECK.

There are measurable radii `R_n`, tending to `0` almost surely, and measurable curves `E_n` such that, for `n ≥ 1`,
`R_n > 0` and `η₀(t/n) = R_n E_n(t)` almost surely, and `E_n` has the law of `η₀`. -/
def ZeroConeCurveDilationLaw (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ (Rsc : ℕ → Ω → ℝ≥0) (E : ℕ → Ω → C(ℝ, ℂ)),
    (∀ n, Measurable (Rsc n)) ∧ (∀ n, Measurable (E n)) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n => Rsc n ω) atTop (𝓝 0)) ∧
    ∀ n : ℕ, 0 < n → (∀ᵐ ω ∂P, 0 < Rsc n ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, η₀ ω (t / (n : ℝ)) = (Rsc n ω : ℝ) • E n ω t) ∧
      P.map (E n) = P.map η₀

/-- **The edge counts of the cells as a dilation-invariant Borel function of the curve** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 53: "For the phase `θ` the rescaled unit cells are exactly
`R_b⁻¹ η₀(b[j − 1 + θ, j + θ])`. Nontrivial common boundary arcs and multiplicities are preserved by this dilation";
`notes/fp-gaps/CODEX-MQ-sbl-15.md`, line 13: the conductances of the cells "are determined by the ordered planar
curve"; Gwynne–Miller–Sheffield, arXiv:1705.11161, (1.2) and the proof of Proposition 2.2; Duplantier–Miller–Sheffield,
arXiv:1409.7055, §8.2). PENDING TRUTH CHECK.

There are a measurable `Ψ` from curves to integer matrices and a set `S` of curves, closed under positive dilations,
on which `Ψ` is invariant under positive dilations, such that for every measurable version `G` of the boundary-length
pair and every `n ≥ 1`, for `P ⊗ Unif[0, 1]`-almost every `(ω, θ)` the curve `t ↦ η₀(ω)((t + θ)/n)` lies in `S` and the
edge counts at mesh `1/n` of `t ↦ G(ω)(t + θ/n)` are `Ψ` of it. -/
def ZeroConeEdgeCountCode (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ (Ψ : C(ℝ, ℂ) → (ℤ → ℤ → ℕ)) (S : Set C(ℝ, ℂ)), Measurable Ψ ∧
    (∀ q ∈ S, ∀ c : ℝ, 0 < c → c • q ∈ S ∧ Ψ (c • q) = Ψ q) ∧
    ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G → ∀ n : ℕ, 0 < n →
      ∀ᵐ p ∂P.prod zeroConePhase, phaseShiftedCurve 1 p.2 (curveMeshRescale n (η₀ p.1)) ∈ S ∧
        phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1) =
          Ψ (phaseShiftedCurve 1 p.2 (curveMeshRescale n (η₀ p.1)))

/-- **The scaling law of the weighted cell data** (written answer `notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 53: "Thus
the rescaled *weighted* unit-mesh data have the original law and their dilation is the original `b`-mesh data") from
the dilation law of the curve and the dilation-invariant code of the edge counts: both weighted data are almost surely
`weightedCurveData Ψ` of (curve, phase), with the curves `E_n` and `η₀` of the same law. -/
theorem zeroConeWeightedMeshScaling_of_curveDilationLaw
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (ha : ZeroConeCurveDilationLaw D hγ) (hb : ZeroConeEdgeCountCode D hγ) :
    ZeroConeWeightedMeshScaling D hγ := by
  intro G hG
  obtain ⟨Rsc, E, hRm, hEm, hR0, hrel⟩ := ha
  obtain ⟨Ψ, S, hΨm, hinv, hcode⟩ := hb
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηm : Measurable η₀ := D.measurable_curves.2.2.1
  refine ⟨Rsc, E, hRm, hEm, hR0, fun n hn => ⟨(hrel n hn).1, (hrel n hn).2.1, ?_⟩⟩
  have hL : (fun p : Ω × ℝ => (phaseShiftedCurve 1 p.2 (E n p.1),
      phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1))) =ᵐ[P.prod zeroConePhase]
      fun p => weightedCurveData Ψ (E n p.1, p.2) := by
    filter_upwards [hcode G hG n hn, Measure.quasiMeasurePreserving_fst.ae (hrel n hn).1,
      Measure.quasiMeasurePreserving_fst.ae (hrel n hn).2.1] with p hp hpos hsc
    obtain ⟨hS, hEq⟩ := hp
    have hR : (0 : ℝ) < (Rsc n p.1 : ℝ) := NNReal.coe_pos.2 hpos
    have hdil := phaseShiftedCurve_curveMeshRescale p.2 hsc
    rw [hdil] at hS hEq
    have hinv' := (hinv _ hS _ (inv_pos.2 hR)).2
    rw [inv_smul_smul₀ hR.ne'] at hinv'
    exact Prod.ext rfl (hEq.trans hinv'.symm)
  have hL1 : phaseShiftedData η₀ G 1 =ᵐ[P.prod zeroConePhase]
      fun p => weightedCurveData Ψ (η₀ p.1, p.2) := by
    filter_upwards [hcode G hG 1 Nat.one_pos] with p hp
    have he := hp.2
    rw [curveMeshRescale_one, Nat.cast_one, div_one] at he
    exact Prod.ext rfl he
  refine (Measure.map_congr hL).trans ?_
  refine Eq.trans ?_ (Measure.map_congr hL1).symm
  rw [map_prod_zeroConePhase_comp P (measurable_weightedCurveData hΨm) (hEm n),
    map_prod_zeroConePhase_comp P (measurable_weightedCurveData hΨm) hηm, (hrel n hn).2.2]

/-- **The strict superlevel events of the uniform errors as projections of Borel events** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 57: "For a fixed integer start `j`, the interpolated walk law is a Borel
kernel in the countable matrix and vertex locations ... the Prokhorov distance is Borel there and agrees with the
original distance"; line 59: "For `A = B̄_ρ ∖ B_b`, the conditions `z ∈ A` and `z ∈ K_j` are Borel jointly in the data
and `z`, also when a positive spatial scale multiplies the cells. In the unit case the strict superlevel event of the
scale supremum is the projection of the Borel event that there exist `0 < s ≤ ε₀`, `z ∈ A`, `j ∈ ℤ` attaining an error
strictly above the threshold with `z ∈ s K_j`. In the mesh case omit `s` and use the fixed `1/n` cells ... Empty
suprema are zero ... This argument includes boundary starts shared by several cells"). PENDING TRUTH CHECK.

On the annuli `closedBall 0 ρ \ B_b(0)`, every strict superlevel set of the scale supremum of the unit-mesh error and of
the mesh-`1/n` error, `n ≥ 1`, is the projection of a Borel subset of (data) × `ℝ × ℂ × ℤ`. -/
def WeightedErrorSuperlevelBorelProjection : Prop :=
  ∀ b ρ : ℝ,
    (∀ (ε₀ : ℝ≥0) (t : ℝ≥0∞), ∃ B : Set ((C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ)), MeasurableSet B ∧
      {w | t < scaleSup (weightedUnitScaleError (closedBall (0 : ℂ) ρ \ ball 0 b)) ε₀ w} = Prod.fst '' B) ∧
    ∀ n : ℕ, 0 < n → ∀ t : ℝ≥0∞, ∃ B : Set ((C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ)), MeasurableSet B ∧
      {w | t < meshUniformError (closedBall (0 : ℂ) ρ \ ball 0 b) (1 / (n : ℝ)) w} = Prod.fst '' B

/-- **Measurability of the uniform errors for the completions of the laws of the weighted data** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-22.md`, line 59: "The parameter and data spaces are standard Borel, so these projections are
analytic, hence measurable in the completion of each indicated law ... Rational thresholds give an a.e.-measurable
function"; Kechris, Theorem 21.10) from the Borel projection form of the superlevel events. -/
theorem zeroConeWeightedUniformErrorMeasurability_of_superlevelProjection
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h : WeightedErrorSuperlevelBorelProjection) : ZeroConeWeightedUniformErrorMeasurability D hγ := by
  intro G _ b ρ
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hpol : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  exact ⟨fun ε₀ => aemeasurable_of_superlevel_eq_image_fst ((h b ρ).1 ε₀) _,
    fun n hn => aemeasurable_of_superlevel_eq_image_fst ((h b ρ).2 n hn) _⟩

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from Theorem 3.10 of arXiv:1807.07515, the dilation law of
the zero-cone curve, the dilation-invariant code of the edge counts and the Borel projection form of the error
events.** -/
theorem zeroConeAnnulusLPForm_of_theorem310_dilation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1 D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) (h310 : GMSTheorem310)
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (ha : ZeroConeCurveDilationLaw D hγ) (hb : ZeroConeEdgeCountCode D hγ)
    (hproj : WeightedErrorSuperlevelBorelProjection) :
    ZeroConeAnnulusLPForm D hγ :=
  zeroConeAnnulusLPForm_of_theorem310_code D hγ hf hI h25 hA1 hcov hlaw hcurve hphase h310 hreal hrot
    (zeroConeWeightedMeshScaling_of_curveDilationLaw D hγ ha hb)
    (zeroConeWeightedUniformErrorMeasurability_of_superlevelProjection D hγ hproj)

end ZeroCone

end MatedCRT.GMS310Transfer
