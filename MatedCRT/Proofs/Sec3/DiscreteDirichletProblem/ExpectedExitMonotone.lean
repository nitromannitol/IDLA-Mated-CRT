import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize

/-! Monotonicity of ordinary exit-time barriers in the domain. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Enlarging a domain increases its ordinary expected exit time. -/
theorem expectedExitTime_mono_domain (m : ℤ → ℤ → ℕ) {I J : Set ℤ}
    (hIJ : I ⊆ J) (a : ℤ) : expectedExitTime m I a ≤ expectedExitTime m J a := by
  unfold expectedExitTime
  apply lintegral_mono
  intro x
  change (vExitTime I x : ℝ≥0∞) ≤ (vExitTime J x : ℝ≥0∞)
  have h := vExitTime_mono_domain hIJ x
  induction hi : vExitTime I x using ENat.recTopCoe with
  | top => simp only [hi, top_le_iff] at h; simp [h]
  | coe i =>
    induction hj : vExitTime J x using ENat.recTopCoe with
    | top => simp
    | coe j =>
      simp only [hi, hj, ENat.natCast_le_natCast] at h
      simpa using (show (i : ℝ≥0∞) ≤ (j : ℝ≥0∞) from Nat.cast_le.mpr h)

/-- On concentric disks, finite ordinary expected exit times give ordered
rescaled barriers. -/
theorem rescale_expectedExitTime_concentric_mono
    {m : ℤ → ℤ → ℕ} {ε c r R : ℝ} {η : ℝ → ℂ} {z x : ℂ}
    (hη : Continuous η) (hrR : r ≤ R) (hc : 0 ≤ c)
    (hfin : expectedExitTime m (interiorCellVertices ε η (ball z R))
      (vertexOf ε η x) ≠ ⊤) :
    rescale c ε η (fun a => (expectedExitTime m
      (interiorCellVertices ε η (ball z r)) a).toReal) x ≤
    rescale c ε η (fun a => (expectedExitTime m
      (interiorCellVertices ε η (ball z R)) a).toReal) x := by
  have hle := expectedExitTime_mono_domain m
    (interiorCellVertices_concentric_ball_mono (ε := ε) hη z hrR) (vertexOf ε η x)
  have hsmall := ne_top_of_le_ne_top hfin hle
  unfold rescale
  exact mul_le_mul_of_nonneg_left ((ENNReal.toReal_le_toReal hsmall hfin).2 hle)
    (inv_nonneg.mpr hc)

/-- Along summable mesh scales, the rescaled exit-time barrier for a disk
is eventually bounded by that for any fixed larger concentric disk. -/
theorem ae_eventual_rescale_expectedExitTime_concentric_mono
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {r R : ℝ} {z : ℂ}
    (hrR : r ≤ R) (hball : ball z R ⊆ ball 0 ρ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ∀ x ∈ ball z R,
      rescale (S.mε (e n)) (e n) (S.η ω) (fun a =>
        (expectedExitTime (S.mult (e n) ω)
          (interiorCellVertices (e n) (S.η ω) (ball z r)) a).toReal) x ≤
      rescale (S.mε (e n)) (e n) (S.η ω) (fun a =>
        (expectedExitTime (S.mult (e n) ω)
          (interiorCellVertices (e n) (S.η ω) (ball z R)) a).toReal) x := by
  filter_upwards [ae_eventual_expectedExit_size_of_statements h218 h217 hγ hγ2 hρ hρ1
    S hS hball e he he0, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hsize harea hp
  obtain ⟨C, hC⟩ := hsize
  filter_upwards [hC] with n hn x hx
  have hcell : vertexOf (e n) (S.η ω) x ∈ cellVertices (e n) (S.η ω) (ball z R) :=
    ⟨x, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 (he.1 n) x, hx⟩
  exact rescale_expectedExitTime_concentric_mono harea.1 hrR (medianOf_nonneg _) (hn _ hcell).1

end MatedCRT

#print axioms MatedCRT.rescale_expectedExitTime_concentric_mono
#print axioms MatedCRT.ae_eventual_rescale_expectedExitTime_concentric_mono
