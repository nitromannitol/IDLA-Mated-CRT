import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapPairingTransport
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2A
import HarmonicBalls.Proposed.MillerSheffieldIG4

/-! # Dirichlet coordinates for whole-plane mean-zero pairings -/

noncomputable section

namespace MatedCRT

open MeasureTheory Set
open LQGMetric QuantumZipper QuantumZipper.K3 LQGMetric.MarkovZB
open scoped RealInnerProductSpace

/-- For the distribution-valued whole-plane GFF, each mean-zero test pairing
has a coordinate in the whole-plane Dirichlet space. Smooth compactly supported
shifts pair with these coordinates by the Dirichlet inner product. -/
theorem exists_wholePlane_dirichlet_pairing_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P) :
    ∃ i : TestC0 → gradClosure ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)),
      (∀ φ : TestC0, ∀ᵐ ω ∂P,
        h ω φ.1 = (cmIso hh ⊤ (i φ)) ω) ∧
      (∀ (f : zsSub ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)) (φ : TestC0),
        inner ℝ (gradLin ⊤ f) (i φ) = ∫ x, φ.1 x * f.1 x) := by
  choose i hi using fun φ : TestC0 => LQGMetric.MarkovGermVer.pair_mem_range_cmIso_top hh φ
  refine ⟨i, ?_, ?_⟩
  · intro φ
    have hφ := (memLp_pair hh φ).coeFn_toLp
    rw [← hi φ] at hφ
    exact hφ.symm
  · intro f φ
    have hcov := inner_cmIso_gradLin hh ⊤ f φ
    rw [← hi φ, LinearIsometry.inner_map_map] at hcov
    exact hcov

/-- The indexed Dirichlet pairing process has the product measurable structure. -/
theorem measurable_wholePlane_dirichlet_pairings
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P) :
    Measurable (fun ω (v : gradClosure ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ))) => (cmIso hh ⊤ v) ω) := by
  exact measurable_pi_iff.mpr fun v => (MeasureTheory.Lp.stronglyMeasurable (cmIso hh ⊤ v)).measurable

/-- The Dirichlet-coordinate process of the whole-plane GFF is a centered
Gaussian process with the Dirichlet inner product as covariance. -/
theorem isGaussian_wholePlane_dirichlet_pairings
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P) :
    HarmonicBalls.IsGaussianOnInnerProductSpace P
      (gradClosure ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
        (zeroSpace ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)))
      (fun v ω => (cmIso hh ⊤ v) ω) := by
  let W := cmIso hh ⊤
  have hmem (v) := cmIso_mem_gaussSpace hh ⊤ v
  have hcenter (v) : ∫ ω, (W v) ω ∂P = 0 :=
    (LQGMetric.MarkovGauss.isCGauss_of_mem_gaussSpace
      (LQGMetric.gaussian_pairProc hh)
      (LQGMetric.centered_pairProc hh) (memLp_pair hh) (hmem v)).2
  refine ⟨?_, hcenter, ?_, ?_, ?_⟩
  · intro v
    exact (MeasureTheory.Lp.stronglyMeasurable (W v)).measurable
  · intro v w a b
    change ∀ᵐ ω ∂P, (W (a • v + b • w)) ω = a * (W v) ω + b * (W w) ω
    rw [map_add, map_smul, map_smul]
    filter_upwards [MeasureTheory.Lp.coeFn_add (a • W v) (b • W w),
      MeasureTheory.Lp.coeFn_smul a (W v), MeasureTheory.Lp.coeFn_smul b (W w)]
      with ω hadd ha hb
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb] using hadd
  · exact LQGMetric.MarkovGauss.isGaussianProcess_of_mem_gaussSpace
      (LQGMetric.gaussian_pairProc hh)
      (LQGMetric.centered_pairProc hh) (memLp_pair hh) W hmem
  · intro v w
    have hv := MeasureTheory.Lp.memLp (W v)
    have hw := MeasureTheory.Lp.memLp (W w)
    have hcov := inner_toLp_eq_cov hv hw (hcenter v)
    rw [MeasureTheory.Lp.toLp_coeFn, MeasureTheory.Lp.toLp_coeFn,
      LinearIsometry.inner_map_map] at hcov
    exact hcov.symm

end MatedCRT
