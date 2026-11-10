import MatedCRT.FirstPass.S5k.Graph.Lap

/-!
# First pass: the countable presentation of `Δw ≤ ν` (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.1 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I): the condition `Δw ≤ ν` on `B_ρ` in (6) holds iff
`Lf ν f (psiTest a) ≤ 0` for all `a` in a countable family `Φ` of nonnegative test functions dense in the image of
`psiTest`. The set of `(ν, f)` satisfying the countable family of inequalities is measurable (Borel).
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

/-- The pair `(φ|_K, Δφ|_K)` of a nonnegative test function. -/
noncomputable def psiTest {ρ : ℝ} (a : NonnegTest ρ) : DiskFun ρ × DiskFun ρ :=
  (restrictDisk a.1 (continuous_of_isTestFunction_laplacian
      (show IsTestFunction (ball (0 : ℂ) ρ) a.1 ∧ 0 ≤ a.1 from a.2).1).1,
   restrictDisk (Δ a.1) (continuous_of_isTestFunction_laplacian
      (show IsTestFunction (ball (0 : ℂ) ρ) a.1 ∧ 0 ≤ a.1 from a.2).1).2)

/-- On a finite measure of the disk, `Lf` at `psiTest a` is `∫ extDisk f · Δφ − ∫ φ dν`. -/
theorem Lf_psiTest {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) (a : NonnegTest ρ) :
    Lf ν f (psiTest a) = (∫ x, extDisk ρ f x * Δ a.1 x) - ∫ x, a.1 x ∂(ν : Measure ℂ) := by
  simp only [Lf, psiTest]
  have e1 : (∫ x, extDisk ρ f x * extDisk ρ (restrictDisk (Δ a.1) (continuous_of_isTestFunction_laplacian
      (show IsTestFunction (ball (0 : ℂ) ρ) a.1 ∧ 0 ≤ a.1 from a.2).1).2) x) =
      ∫ x, extDisk ρ f x * Δ a.1 x := by
    congr 1
    funext x
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [extDisk_restrictDisk_of_mem _ hx]
    · rw [extDisk_apply_of_notMem f hx, zero_mul, zero_mul]
  have e2 : (∫ x, extDisk ρ (restrictDisk a.1 (continuous_of_isTestFunction_laplacian
      (show IsTestFunction (ball (0 : ℂ) ρ) a.1 ∧ 0 ≤ a.1 from a.2).1).1) x ∂(ν : Measure ℂ)) =
      ∫ x, a.1 x ∂(ν : Measure ℂ) := by
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂(ν : Measure ℂ), x ∈ closedBall (0 : ℂ) ρ := by
      rw [← ν.2.2]
      exact ae_restrict_mem measurableSet_closedBall
    filter_upwards [hae] with x hx
    exact extDisk_restrictDisk_of_mem _ hx
  rw [e1, e2]

/-- `f ↦ ∫ extDisk f · extDisk b` is continuous on `C(K)`. -/
theorem continuous_integral_extDisk_mul_left {ρ : ℝ} (b : DiskFun ρ) :
    Continuous fun f : DiskFun ρ => ∫ x, extDisk ρ f x * extDisk ρ b x := by
  refine continuous_of_abs_sub_le_mul (C := ‖b‖ * (volume (closedBall (0 : ℂ) ρ)).toReal) fun f f' => ?_
  have h := abs_integral_extDisk_mul_sub_le_left f f' b
  rw [dist_eq_norm, mul_comm ‖b‖]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The existence of a countable dense family of nonnegative test functions for `psiTest`. -/
theorem exists_countable_psiTest (ρ : ℝ) :
    ∃ Φ : Set (NonnegTest ρ), Φ.Countable ∧ ∀ a, psiTest a ∈ closure (psiTest '' Φ) := by
  obtain ⟨Φ, -, hc, hd⟩ := exists_countable_dense_family (univ : Set (NonnegTest ρ)) psiTest
  exact ⟨Φ, hc, fun a => hd a (mem_univ a)⟩

/-- **Countable presentation of `Δw ≤ ν`.** For a finite measure `ν` on `B̄_ρ` and `f ∈ C(B̄_ρ)`, the distributional
inequality `Δ(extDisk f) ≤ ν` on `B_ρ` holds iff `Lf ν f (psiTest a) ≤ 0` for all `a` in a family `Φ` whose
`psiTest`-image is dense. -/
theorem laplacianLE_extDisk_iff {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) {Φ : Set (NonnegTest ρ)}
    (hΦ : ∀ a, psiTest a ∈ closure (psiTest '' Φ)) :
    LaplacianLE (extDisk ρ f) (ν : Measure ℂ) (ball (0 : ℂ) ρ) ↔ ∀ a ∈ Φ, Lf ν f (psiTest a) ≤ 0 := by
  have : IsFiniteMeasure (ν : Measure ℂ) := ν.2.1
  constructor
  · intro hL a _
    have hφ := (show IsTestFunction (ball (0 : ℂ) ρ) a.1 ∧ 0 ≤ a.1 from a.2)
    have hint : Integrable a.1 (ν : Measure ℂ) :=
      (continuous_of_isTestFunction_laplacian hφ.1).1.integrable_of_hasCompactSupport hφ.1.2.1
    have := hL.2 a.1 hφ.1 hφ.2 hint
    rw [Lf_psiTest]
    linarith
  · intro hΦ'
    refine ⟨locallyIntegrableOn_extDisk f, fun φ hφ hφ0 _ => ?_⟩
    let a : NonnegTest ρ := ⟨φ, ⟨hφ, hφ0⟩⟩
    have hcl : psiTest a ∈ {y | Lf ν f y ≤ 0} :=
      closure_minimal (by rintro _ ⟨b, hb, rfl⟩; exact hΦ' b hb)
        (isClosed_le (continuous_Lf ν f) continuous_const) (hΦ a)
    have h0 : Lf ν f (psiTest a) ≤ 0 := hcl
    rw [Lf_psiTest] at h0
    linarith

/-- **Measurability of the countable presentation.** The set of `(ν, f)` satisfying `Lf ν f (psiTest a) ≤ 0` for all
`a` in a countable family is measurable in `FinMeasDisk ρ × C(B̄_ρ, ℝ)`. -/
theorem measurableSet_laplacianLE_family {ρ : ℝ} {Φ : Set (NonnegTest ρ)} (hΦ : Φ.Countable) :
    MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | ∀ a ∈ Φ, Lf p.1 p.2 (psiTest a) ≤ 0} := by
  have hpt : ∀ a : NonnegTest ρ, MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | Lf p.1 p.2 (psiTest a) ≤ 0} := by
    intro a
    have hA : Measurable fun p : FinMeasDisk ρ × DiskFun ρ =>
        ∫ x, extDisk ρ p.2 x * extDisk ρ (psiTest a).2 x :=
      (continuous_integral_extDisk_mul_left (psiTest a).2).measurable.comp measurable_snd
    have hB : Measurable fun p : FinMeasDisk ρ × DiskFun ρ =>
        ∫ x, extDisk ρ (psiTest a).1 x ∂(p.1 : Measure ℂ) :=
      measurable_integral_finMeasDisk (a := fun x => extDisk ρ (psiTest a).1 x)
        (measurable_extDisk _) (C := ‖(psiTest a).1‖) (fun x => abs_extDisk_le _ x) |>.comp measurable_fst
    exact measurableSet_le (hA.sub hB) measurable_const
  have : {p : FinMeasDisk ρ × DiskFun ρ | ∀ a ∈ Φ, Lf p.1 p.2 (psiTest a) ≤ 0} =
      ⋂ a ∈ Φ, {p : FinMeasDisk ρ × DiskFun ρ | Lf p.1 p.2 (psiTest a) ≤ 0} := by
    ext p
    simp
  rw [this]
  exact MeasurableSet.biInter hΦ fun a _ => hpt a

end MatedCRT
