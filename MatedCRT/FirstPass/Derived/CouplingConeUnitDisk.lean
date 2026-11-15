import MatedCRT.FirstPass.Derived.CouplingConditionedPath
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare

/-! # The cone field on the unit disk -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- On the coupling's sample space, the cone field agrees on the unit disk
with a normalized whole-plane GFF plus its logarithmic singularity. The
pairing identity holds for all test functions on one common event. -/
theorem exists_normalizedGFF_cone_unitDisk_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Y : Ω → LQGMetric.DistC, LQGMetric.IsNormalizedWPGFF Y P ∧
      ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC,
        (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
        MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ =
        Y ω φ + ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  obtain ⟨Y, hY, hdec⟩ := MatedCRTHarmonic.GMCFacts.exists_cone_decomposition
    hγ D.gff D.bm_B D.bm_B' D.indep_cone hγ2
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hdec] with ω hω
  obtain ⟨g, hfield, hgm, hgl, hgc, hgdisk⟩ := hω
  intro φ hφ
  change MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω)
    (fun u => B u ω) (fun u => B' u ω) φ = _
  rw [hfield, add_apply, MatedCRTHarmonic.MoTPort.ConeCirc.ofFunC_apply' hgl]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : ‖z‖ ≤ 1
  · rw [hgdisk z hz]
  · rw [hφ z (lt_of_not_ge hz), zero_mul, zero_mul]
