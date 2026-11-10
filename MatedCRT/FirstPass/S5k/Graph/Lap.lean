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

theorem locallyIntegrableOn_extDisk {ρ : ℝ} (f : DiskFun ρ) :
    LocallyIntegrableOn (extDisk ρ f) (ball (0 : ℂ) ρ) :=
  ((continuousOn_extDisk f).mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball

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

/-- **Lipschitz bound in the Laplacian slot.** Changing `b` to `b'` changes `∫ extDisk f · extDisk b` by at most
`‖f‖ ‖b - b'‖ vol(K)`. -/
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
      rw [Real.norm_eq_abs] at h
      rw [extDisk_apply_of_mem b hx, extDisk_apply_of_mem b' hx, ← ContinuousMap.sub_apply]
      exact h
    · rw [indicator_of_notMem hx]
      simp [extDisk_apply_of_notMem _ hx]
  have hI : Integrable ((closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f‖ * ‖b - b'‖)) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  refine (norm_integral_le_of_norm_le hI (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real]
  ring

/-- **Lipschitz bound in the `f`-slot.** Changing `f` to `f'` changes `∫ extDisk f · extDisk b` by at most
`‖f - f'‖ ‖b‖ vol(K)`. -/
theorem abs_integral_extDisk_mul_sub_le_left {ρ : ℝ} (f f' b : DiskFun ρ) :
    |(∫ x, extDisk ρ f x * extDisk ρ b x) - ∫ x, extDisk ρ f' x * extDisk ρ b x| ≤
      ‖f - f'‖ * ‖b‖ * (volume (closedBall (0 : ℂ) ρ)).toReal := by
  rw [← integral_sub (integrable_extDisk_mul f b) (integrable_extDisk_mul f' b), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖extDisk ρ f x * extDisk ρ b x - extDisk ρ f' x * extDisk ρ b x‖ ≤
      (closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f - f'‖ * ‖b‖) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [indicator_of_mem hx, Real.norm_eq_abs, ← sub_mul, abs_mul]
      refine mul_le_mul ?_ (abs_extDisk_le b x) (abs_nonneg _) (norm_nonneg _)
      have h := (f - f').norm_coe_le_norm ⟨x, hx⟩
      rw [Real.norm_eq_abs] at h
      rw [extDisk_apply_of_mem f hx, extDisk_apply_of_mem f' hx, ← ContinuousMap.sub_apply]
      exact h
    · rw [indicator_of_notMem hx]
      simp [extDisk_apply_of_notMem _ hx]
  have hI : Integrable ((closedBall (0 : ℂ) ρ).indicator (fun _ => ‖f - f'‖ * ‖b‖)) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  refine (norm_integral_le_of_norm_le hI (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real]
  ring

/-- **Lipschitz bound in the measure slot.** For a finite measure `ν` on `B̄_ρ`,
`|∫ extDisk a dν - ∫ extDisk a' dν| ≤ ‖a - a'‖ ν(B̄_ρ)`. -/
theorem abs_integral_extDisk_sub_le_measure {ρ : ℝ} (ν : FinMeasDisk ρ) (a a' : DiskFun ρ) :
    |(∫ x, extDisk ρ a x ∂(ν : Measure ℂ)) - ∫ x, extDisk ρ a' x ∂(ν : Measure ℂ)| ≤
      ‖a - a'‖ * (ν : Measure ℂ).real univ := by
  have : IsFiniteMeasure (ν : Measure ℂ) := ν.2.1
  have hint : ∀ c : DiskFun ρ, Integrable (fun x => extDisk ρ c x) (ν : Measure ℂ) := fun c =>
    Integrable.of_bound (measurable_extDisk c).aestronglyMeasurable ‖c‖
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_extDisk_le c x)
  rw [← integral_sub (hint a) (hint a'), ← Real.norm_eq_abs]
  have hae : ∀ᵐ x ∂(ν : Measure ℂ), x ∈ closedBall (0 : ℂ) ρ := by
    rw [← ν.2.2]
    exact ae_restrict_mem measurableSet_closedBall
  refine norm_integral_le_of_norm_le_const ?_
  filter_upwards [hae] with x hx
  rw [extDisk_apply_of_mem a hx, extDisk_apply_of_mem a' hx, ← ContinuousMap.sub_apply]
  exact (a - a').norm_coe_le_norm ⟨x, hx⟩

/-- The functional of the Laplacian inequality: `(a, b) ↦ ∫ extDisk f · extDisk b − ∫ extDisk a dν`. -/
noncomputable def Lf {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) (y : DiskFun ρ × DiskFun ρ) : ℝ :=
  (∫ x, extDisk ρ f x * extDisk ρ y.2 x) - ∫ x, extDisk ρ y.1 x ∂(ν : Measure ℂ)

/-- A real function on a pseudo-metric space with a linear modulus of continuity is continuous. -/
theorem continuous_of_abs_sub_le_mul {X : Type*} [PseudoMetricSpace X] {F : X → ℝ} {C : ℝ}
    (h : ∀ x y, |F x - F y| ≤ C * dist x y) : Continuous F := by
  refine LipschitzWith.continuous (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun x y => ?_)
  rw [Real.dist_eq, Real.coe_toNNReal']
  refine (h x y).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) dist_nonneg)

/-- The sum-of-differences inequality for the two-term functional. -/
theorem abs_sub_sub_le_add (A B A' B' : ℝ) : |(A - B) - (A' - B')| ≤ |A - A'| + |B - B'| := by
  rw [show (A - B) - (A' - B') = (A - A') - (B - B') by ring]
  exact abs_sub _ _

theorem continuous_Lf {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) : Continuous (Lf ν f) := by
  refine continuous_of_abs_sub_le_mul (C := ‖f‖ * (volume (closedBall (0 : ℂ) ρ)).toReal +
    (ν : Measure ℂ).real univ) fun y y' => ?_
  unfold Lf
  have h1 := abs_integral_extDisk_mul_sub_le f y.2 y'.2
  have h2 := abs_integral_extDisk_sub_le_measure ν y.1 y'.1
  have hd1 : ‖y.2 - y'.2‖ ≤ dist y y' := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  have hd2 : ‖y.1 - y'.1‖ ≤ dist y y' := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have hvol : 0 ≤ (volume (closedBall (0 : ℂ) ρ)).toReal := ENNReal.toReal_nonneg
  have hν : 0 ≤ (ν : Measure ℂ).real univ := measureReal_nonneg
  have hf : 0 ≤ ‖f‖ := norm_nonneg _
  have key := abs_sub_sub_le_add (∫ x, extDisk ρ f x * extDisk ρ y.2 x)
    (∫ x, extDisk ρ y.1 x ∂(ν : Measure ℂ)) (∫ x, extDisk ρ f x * extDisk ρ y'.2 x)
    (∫ x, extDisk ρ y'.1 x ∂(ν : Measure ℂ))
  refine key.trans ((add_le_add h1 h2).trans ?_)
  nlinarith [mul_le_mul_of_nonneg_left hd1 (mul_nonneg hf hvol),
    mul_le_mul_of_nonneg_left hd2 hν, dist_nonneg (x := y) (y := y')]

end MatedCRT
