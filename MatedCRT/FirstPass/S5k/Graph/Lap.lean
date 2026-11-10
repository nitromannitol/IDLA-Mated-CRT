import MatedCRT.FirstPass.S5k.Graph.Basic
import HarmonicBalls.Steps.Sec3.Basic

/-!
# First pass: countable presentation of `Δw ≤ ν` in the Borel graph (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.1 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I), the condition `Δw ≤ ν` on `B_ρ` of (6): it is equivalent to
`∫ w Δφ ≤ ∫ φ dν` for the nonnegative test functions `φ` on `B_ρ`, and it suffices to test a countable family of them,
dense in the topology of `(φ|_K, Δφ|_K) ∈ C(K) × C(K)`. The functional `Lf` below is Lipschitz in that topology, so the
inequality for the dense family implies it for all test functions.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

/-- Nonnegative test functions on the open disk `B_ρ`. -/
def NonnegTest (ρ : ℝ) : Set (ℂ → ℝ) := {φ | IsTestFunction (ball (0 : ℂ) ρ) φ ∧ 0 ≤ φ}

theorem continuous_of_isTestFunction_laplacian {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTestFunction U φ) :
    Continuous φ ∧ Continuous (Δ φ) :=
  ⟨h.1.continuous, continuous_laplacian_of_contDiff (h.1.of_le (by norm_cast))⟩

/-- Restriction of a continuous function on `ℂ` to the closed disk. -/
def restrictDisk {ρ : ℝ} (g : ℂ → ℝ) (hg : Continuous g) : DiskFun ρ :=
  ⟨fun x => g x, hg.comp continuous_subtype_val⟩

theorem extDisk_restrictDisk_of_mem {ρ : ℝ} {g : ℂ → ℝ} (hg : Continuous g) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) ρ) : extDisk ρ (restrictDisk g hg) x = g x := by
  rw [extDisk_apply_of_mem _ hx]
  rfl

/-- `|extDisk f x| ≤ ‖f‖` for every `x`. -/
theorem abs_extDisk_le {ρ : ℝ} (f : DiskFun ρ) (x : ℂ) : |extDisk ρ f x| ≤ ‖f‖ := by
  by_cases hx : x ∈ closedBall (0 : ℂ) ρ
  · rw [extDisk_apply_of_mem f hx, ← Real.norm_eq_abs]
    exact f.norm_coe_le_norm ⟨x, hx⟩
  · rw [extDisk_apply_of_notMem f hx]
    simp [norm_nonneg]

/-- The extension by zero is `Function.extend` of the inclusion of the closed disk, hence measurable. -/
theorem extDisk_eq_extend {ρ : ℝ} (f : DiskFun ρ) :
    extDisk ρ f = Function.extend (Subtype.val : closedBall (0 : ℂ) ρ → ℂ) f (fun _ => 0) := by
  funext x
  by_cases hx : x ∈ closedBall (0 : ℂ) ρ
  · have hx' : x = ((⟨x, hx⟩ : closedBall (0 : ℂ) ρ) : ℂ) := rfl
    rw [hx', Subtype.val_injective.extend_apply, extDisk_apply_of_mem f hx]
  · rw [extDisk_apply_of_notMem f hx, Function.extend_apply']
    rintro ⟨y, rfl⟩
    exact hx y.2

theorem measurable_extDisk {ρ : ℝ} (f : DiskFun ρ) : Measurable (extDisk ρ f) := by
  rw [extDisk_eq_extend]
  exact (MeasurableEmbedding.subtype_coe measurableSet_closedBall).measurable_extend
    f.continuous.measurable measurable_const

theorem integrable_extDisk_mul {ρ : ℝ} (f b : DiskFun ρ) :
    Integrable fun x => extDisk ρ f x * extDisk ρ b x := by
  refine Integrable.mono' (g := (closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f‖ * ‖b‖)) ?_ ?_ ?_
  · exact (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  · exact ((measurable_extDisk f).mul (measurable_extDisk b)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_extDisk_le f x) (abs_extDisk_le b x) (abs_nonneg _) (norm_nonneg _)
    · rw [indicator_of_notMem hx]
      simp [extDisk_apply_of_notMem _ hx]

/-- **Lipschitz bound in the test function.** Changing the Laplacian slot `b` by `b'` changes
`∫ extDisk f · extDisk b` by at most `‖f‖ ‖b - b'‖ vol(K)`. -/
theorem abs_integral_extDisk_mul_sub_le {ρ : ℝ} (f b b' : DiskFun ρ) :
    |(∫ x, extDisk ρ f x * extDisk ρ b x) - ∫ x, extDisk ρ f x * extDisk ρ b' x| ≤
      ‖f‖ * ‖b - b'‖ * (volume (closedBall (0 : ℂ) ρ)).toReal := by
  rw [← integral_sub (integrable_extDisk_mul f b) (integrable_extDisk_mul f b'), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖extDisk ρ f x * extDisk ρ b x - extDisk ρ f x * extDisk ρ b' x‖ ≤
      (closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f‖ * ‖b - b'‖) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [indicator_of_mem hx, Real.norm_eq_abs, ← mul_sub, abs_mul]
      refine mul_le_mul (abs_extDisk_le f x) ?_ (abs_nonneg _) (norm_nonneg _)
      have h := (b - b').norm_coe_le_norm ⟨x, hx⟩
      rw [ContinuousMap.sub_apply, Real.norm_eq_abs, extDisk_apply_of_mem b hx,
        extDisk_apply_of_mem b' hx, ← Real.norm_eq_abs] at *
      rw [← ContinuousMap.sub_apply]
      exact h
    · rw [indicator_of_notMem hx]
      simp [extDisk_apply_of_notMem _ hx]
  have hI : Integrable ((closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f‖ * ‖b - b'‖)) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  refine (norm_integral_le_of_norm_le hI (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real]
  ring

end MatedCRT
