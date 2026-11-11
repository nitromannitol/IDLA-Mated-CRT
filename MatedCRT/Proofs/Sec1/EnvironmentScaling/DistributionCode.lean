import MatedCRT.Proofs.Sec1.EnvironmentScaling
import MatedCRT.Proofs.Measurability.FieldCircle
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange

/-!
# Countable coding of plane distributions

The reconstruction portion.  The countable Borel code is supplied by Bonanno’s construction; no completion
of the field sigma-algebra is used.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Distributions
open HarmonicBalls

namespace MatedCRT.Sec1

/-- A countable family of actual plane tests whose evaluation map is a
measurable embedding for the cylinder sigma-algebra on distributions. -/
structure PlaneDistributionCode where
  test : LQGMetric.CoordJ → LQGMetric.TestC
  embedding : MeasurableEmbedding (fun (d : LQGMetric.DistC) (n : LQGMetric.CoordJ) => d (test n))

/-- Bonanno's code proves the countable reconstruction boundary. Its Borel
range is proved by local finite-order bounds and extension on each compact. -/
def planeDistributionCode : PlaneDistributionCode where
  test := LQGMetric.comb ⊤
  embedding := LQGMetric.measurableEmbedding_pairJ ⊤

/-- Decode a valid sequence and return the zero distribution otherwise. -/
def PlaneDistributionCode.decode (C : PlaneDistributionCode) : (LQGMetric.CoordJ → ℝ) → LQGMetric.DistC :=
  Function.extend (fun (d : LQGMetric.DistC) (n : LQGMetric.CoordJ) => d (C.test n)) id (fun _ => 0)

theorem PlaneDistributionCode.measurable_decode (C : PlaneDistributionCode) :
    Measurable C.decode :=
  C.embedding.measurable_extend measurable_id measurable_const

theorem PlaneDistributionCode.decode_encode (C : PlaneDistributionCode) (d : LQGMetric.DistC) :
    C.decode (fun n => d (C.test n)) = d :=
  C.embedding.injective.extend_apply id (fun _ => 0) d

/-- A countable code gives a distribution measurable for the exact field
sigma-algebra and recovers simultaneously all pairings on the representation
event.  The representing distribution need not be measurable. -/
theorem exists_fieldMeasurable_distribution (C : PlaneDistributionCode)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (H : Ω → LQGMetric.DistC)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∃ Hhat : Ω → LQGMetric.DistC,
      Measurable[S.fieldSigma] Hhat ∧
      ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = Hhat ω φ := by
  let coords : Ω → LQGMetric.CoordJ → ℝ := fun ω n => S.hC ω (C.test n)
  have hm' : ∀ n, Measurable[S.fieldSigma] fun ω => coords ω n := by
    intro n
    exact FieldCircle.measurable_hC_fieldSigma S
      ⟨(C.test n).contDiff, (C.test n).hasCompactSupport, (C.test n).tsupport_subset⟩
  have hm : Measurable[S.fieldSigma] coords := by
    let m := S.fieldSigma
    let : MeasurableSpace Ω := m
    exact measurable_pi_iff.mpr hm'
  have hdecode : Measurable[S.fieldSigma] (C.decode ∘ coords) := by
    let m := S.fieldSigma
    let : MeasurableSpace Ω := m
    exact C.measurable_decode.comp hm
  refine ⟨C.decode ∘ coords, hdecode, ?_⟩
  filter_upwards [hrep] with ω hω
  have heq : coords ω = fun n => H ω (C.test n) := by
    funext n
    simpa only [coords] using hω (C.test n)
  intro φ
  change S.hC ω φ = C.decode (coords ω) φ
  rw [heq, C.decode_encode]
  exact hω φ

/-- The mating-of-trees field gives the simultaneous representation required
by the reconstruction, without choosing separate null sets for tests. -/
theorem MatedCRTEnv.IsValid.ae_coneField_representation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC,
      ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, ha⟩ := hS.matingOfTrees
  refine ⟨fun ω => MatedCRTHarmonic.MatedCRT.coneField (X ω)
    (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), ?_⟩
  filter_upwards [ha] with ω hω
  exact hω.2

/-- Validity supplies the common representation event, and the Borel code
then gives a representative measurable for `S.fieldSigma`. -/
theorem exists_fieldMeasurable_coneDistribution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ Hhat : Ω → LQGMetric.DistC,
      Measurable[S.fieldSigma] Hhat ∧
      ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = Hhat ω φ := by
  obtain ⟨H, hrep⟩ := MatedCRTEnv.IsValid.ae_coneField_representation hS
  exact exists_fieldMeasurable_distribution planeDistributionCode S H hrep

end MatedCRT.Sec1
