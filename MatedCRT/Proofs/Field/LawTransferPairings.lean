import MatedCRT.Steps.Sec6.AnnulusIterate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# Local σ-algebras of mean-zero pairings

The two descriptions of the GFF use the same local test functions. We compare their
σ-algebras and the shifted restrictions used in Leonardo Bonanno's proof of the
Gwynne–Miller annulus estimate.
-/

namespace MatedCRT.Field

open MeasureTheory Set HarmonicBalls

/-- The local process of mean-zero pairings in the Harmonic Balls formulation. -/
noncomputable def localPairings {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (ω : Ω) (φ : {φ : LQGMetric.TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ U}) : ℝ :=
  hC ω φ.1.1

/-- The local pairing process generates the modulo-constants σ-algebra. -/
theorem modConstSigma_eq_localPairings {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    modConstSigma hC U = MeasurableSpace.comap (localPairings hC U) inferInstance := by
  apply le_antisymm
  · refine iSup_le fun φ => iSup_le fun hφ => ?_
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1.1, hφ.1.2.1, subset_univ _⟩
    let t : {φ : LQGMetric.TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ U} :=
      ⟨⟨ψ, hφ.2⟩, hφ.1.2.2⟩
    apply measurable_iff_comap_le.mp
    have hm : Measurable[MeasurableSpace.comap (localPairings hC U) inferInstance]
        (localPairings hC U) := fun _ hs => ⟨_, hs, rfl⟩
    exact (measurable_pi_apply t).comp hm
  · let : MeasurableSpace Ω := modConstSigma hC U
    apply measurable_iff_comap_le.mp
    refine measurable_pi_iff.mpr fun φ => ?_
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (φ.1.1 : ℂ → ℝ) (le_iSup_of_le
      ⟨⟨φ.1.1.contDiff, φ.1.1.hasCompactSupport, φ.2⟩, φ.1.2⟩ le_rfl)

/-- Local mean-zero pairings are measurable with respect to the restriction of any
constant shift of the distribution-valued field. -/
theorem localPairings_le_shifted_fieldSigma {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → LQGMetric.DistC) (c : Ω → ℝ) (U : TopologicalSpace.Opens ℂ) :
    LQGMetric.Blueprint.fieldSigma0On h U ≤
      LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) U := by
  let : MeasurableSpace Ω := LQGMetric.Blueprint.fieldSigma
    (fun ω => LQGMetric.addConst (h ω) (c ω)) U
  apply measurable_iff_comap_le.mp
  refine measurable_pi_iff.mpr fun φ => ?_
  let ψ : LQGMetric.TestOn U := ⟨φ.1.1, φ.1.1.contDiff, φ.1.1.hasCompactSupport, φ.2⟩
  have heq : (TestFunction.monoCLM ℝ ψ : LQGMetric.TestC) = φ.1.1 := by
    ext x
    simp [ψ, TestFunction.monoCLM_apply]
  have hm : Measurable[LQGMetric.Blueprint.fieldSigma
      (fun ω => LQGMetric.addConst (h ω) (c ω)) U]
      (fun ω => LQGMetric.restrictTo U (LQGMetric.addConst (h ω) (c ω))) :=
    fun _ hs => ⟨_, hs, rfl⟩
  have heval : Measurable (fun g : LQGMetric.DistOn U => g ψ) := by
    have hbase : Measurable (fun (g : LQGMetric.DistOn U) (φ : LQGMetric.TestOn U) => g φ) :=
      fun _ hs => ⟨_, hs, rfl⟩
    exact (measurable_pi_apply ψ).comp hbase
  have hm' := heval.comp hm
  have hv : (fun ω => LQGMetric.restrictTo U (LQGMetric.addConst (h ω) (c ω)) ψ) =
      fun ω => h ω φ.1.1 := by
    funext ω
    change LQGMetric.addConst (h ω) (c ω) (TestFunction.monoCLM ℝ ψ) = _
    rw [heq, LQGMetric.GFFInv.addConst_apply, φ.1.2, zero_mul, add_zero]
  rw [← hv]
  exact hm'

end MatedCRT.Field
