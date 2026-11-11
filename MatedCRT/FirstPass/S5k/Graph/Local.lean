import MatedCRT.FirstPass.S5k.Graph.LapCount
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# First pass: localization of the distributional identity

The condition `Δw = ν` on the cluster `U_w` in (6) is a
distributional identity on the open set `U_w`. It is tested on countably many disks; passing from disks to `U_w` is the
localization principle: a linear identity valid for test functions supported in each member of an open cover of `U`
holds for test functions supported in `U`, by a finite smooth partition of unity (`SmoothPartitionOfUnity`).
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

/-- The pair `(φ|_K, Δφ|_K)` of any test function on an open set `U`. -/
noncomputable def psiOn {ρ : ℝ} {U : Set ℂ} (a : {φ : ℂ → ℝ // IsTestFunction U φ}) : DiskFun ρ × DiskFun ρ :=
  (restrictDisk a.1 (continuous_of_isTestFunction_laplacian a.2).1,
   restrictDisk (Δ a.1) (continuous_of_isTestFunction_laplacian a.2).2)

/-- On a finite measure of the disk, `Lf` at `psiOn a` is `∫ extDisk f · Δφ − ∫ φ dν`, for any test function. -/
theorem Lf_psiOn {ρ : ℝ} {U : Set ℂ} (ν : FinMeasDisk ρ) (f : DiskFun ρ)
    (a : {φ : ℂ → ℝ // IsTestFunction U φ}) :
    Lf ν f (psiOn (ρ := ρ) a) = (∫ x, extDisk ρ f x * Δ a.1 x) - ∫ x, a.1 x ∂(ν : Measure ℂ) := by
  simp only [Lf, psiOn]
  have e1 : (∫ x, extDisk ρ f x * extDisk ρ (restrictDisk (Δ a.1) (continuous_of_isTestFunction_laplacian a.2).2) x) =
      ∫ x, extDisk ρ f x * Δ a.1 x := by
    congr 1
    funext x
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [extDisk_restrictDisk_of_mem _ hx]
    · rw [extDisk_apply_of_notMem f hx, zero_mul, zero_mul]
  have e2 : (∫ x, extDisk ρ (restrictDisk a.1 (continuous_of_isTestFunction_laplacian a.2).1) x ∂(ν : Measure ℂ)) =
      ∫ x, a.1 x ∂(ν : Measure ℂ) := by
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂(ν : Measure ℂ), x ∈ closedBall (0 : ℂ) ρ := by
      rw [← ν.2.2]
      exact ae_restrict_mem measurableSet_closedBall
    filter_upwards [hae] with x hx
    exact extDisk_restrictDisk_of_mem _ hx
  rw [e1, e2]

/-- The zero function is a test function on any open set. -/
theorem isTestFunction_zero (U : Set ℂ) : IsTestFunction U (fun _ => (0 : ℝ)) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

/-- A sum of two test functions on `U` is a test function on `U`. -/
theorem isTestFunction_add {U : Set ℂ} {φ ψ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hψ : IsTestFunction U ψ) :
    IsTestFunction U (fun x => φ x + ψ x) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

/-- The distributional functional `φ ↦ ∫ extDisk f · Δφ − ∫ φ dν` on test functions. -/
noncomputable def Lt {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) (φ : ℂ → ℝ) : ℝ :=
  (∫ x, extDisk ρ f x * Δ φ x) - ∫ x, φ x ∂(ν : Measure ℂ)

/-- `Lt` is additive on test functions on `U ⊆ B_ρ`. -/
theorem Lt_add {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) {U : Set ℂ} (hU : U ⊆ ball (0 : ℂ) ρ)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hψ : IsTestFunction U ψ) :
    Lt ν f (fun x => φ x + ψ x) = Lt ν f φ + Lt ν f ψ := by
  have : IsFiniteMeasure (ν : Measure ℂ) := ν.2.1
  have hLI : LocallyIntegrableOn (extDisk ρ f) U :=
    (locallyIntegrableOn_extDisk f).mono_set hU
  have hΔ : Δ (fun x => φ x + ψ x) = fun x => Δ φ x + Δ ψ x := by
    funext x
    exact (ContDiffAt.laplacian_add ((hφ.1.of_le (by norm_cast)).contDiffAt)
      ((hψ.1.of_le (by norm_cast)).contDiffAt) : _)
  have hi1 := integrable_mul_laplacian_of_test hLI hφ
  have hi2 := integrable_mul_laplacian_of_test hLI hψ
  have hm1 : Integrable φ (ν : Measure ℂ) :=
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hm2 : Integrable ψ (ν : Measure ℂ) :=
    hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  unfold Lt
  rw [hΔ]
  simp only [mul_add]
  rw [integral_add hi1 hi2, integral_add hm1 hm2]
  ring

/-- `Lt` vanishes on the zero function. -/
theorem Lt_zero {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) : Lt ν f (fun _ => (0 : ℝ)) = 0 := by
  unfold Lt
  simp

/-- A finite sum of test functions on `U` is a test function on `U`. -/
theorem isTestFunction_finsum {U : Set ℂ} {ι : Type*} [DecidableEq ι] (t : Finset ι) (g : ι → ℂ → ℝ)
    (hg : ∀ i ∈ t, IsTestFunction U (g i)) : IsTestFunction U (fun x => ∑ i ∈ t, g i x) := by
  induction t using Finset.induction_on with
  | empty => exact isTestFunction_zero U
  | insert j t hj ih =>
    have e : (fun x => ∑ i ∈ insert j t, g i x) = fun x => g j x + ∑ i ∈ t, g i x := by
      funext x
      rw [Finset.sum_insert hj]
    rw [e]
    exact isTestFunction_add (hg j (Finset.mem_insert_self j t))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- **Localization.** Let `L` be additive on test functions on `U`, vanish at `0`, and vanish on test functions supported
in each member of an open cover `D_i ⊆ U` of `U`. Then `L` vanishes on all test functions supported in `U`. -/
theorem vanish_of_local {U : Set ℂ} {ι : Type*} [DecidableEq ι] (D : ι → Set ℂ) (hD : ∀ i, IsOpen (D i))
    (hDU : ∀ i, D i ⊆ U) (hU : U ⊆ ⋃ i, D i) (L : (ℂ → ℝ) → ℝ)
    (hadd : ∀ φ ψ : ℂ → ℝ, IsTestFunction U φ → IsTestFunction U ψ → L (fun x => φ x + ψ x) = L φ + L ψ)
    (hzero : L (fun _ => 0) = 0)
    (hloc : ∀ i, ∀ φ : ℂ → ℝ, IsTestFunction (D i) φ → L φ = 0) :
    ∀ φ : ℂ → ℝ, IsTestFunction U φ → L φ = 0 := by
  intro φ hφ
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have hsub : tsupport φ ⊆ ⋃ i, D i := hφ.2.2.trans hU
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover D hD hsub
  have hs' : tsupport φ ⊆ ⋃ i : s, D i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hs hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := modelWithCornersSelf ℝ ℂ) hK.isClosed (fun i : s => D i)
    (fun i => hD i) hs'
  have hsplit : φ = fun x => ∑ i : s, χ i x * φ x := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have h1 : ∑ i : s, χ i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact χ.sum_eq_one hx
      rw [← Finset.sum_mul, h1, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hpieces : ∀ i : s, IsTestFunction (D i) (fun x => χ i x * φ x) := by
    intro i
    refine ⟨(contMDiff_iff_contDiff.1 (χ i).contMDiff).mul hφ.1, hφ.2.1.mul_left, ?_⟩
    exact tsupport_mul_subset_left.trans (hχ i)
  have hpU : ∀ i : s, IsTestFunction U (fun x => χ i x * φ x) := fun i =>
    isTestFunction_of_subset (hpieces i) (hDU i)
  have hsum : ∀ t : Finset s, L (fun x => ∑ i ∈ t, χ i x * φ x) = ∑ i ∈ t, L (fun x => χ i x * φ x) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have e : (fun x => ∑ i ∈ (∅ : Finset s), χ i x * φ x) = fun _ => 0 := by
        funext x
        simp
      rw [e, hzero]
      simp
    | insert j t hj ih =>
      have h1 := hpU j
      have h2 : IsTestFunction U (fun x => ∑ i ∈ t, χ i x * φ x) :=
        isTestFunction_finsum t (fun i x => χ i x * φ x) fun i _ => hpU i
      have e : (fun x => ∑ i ∈ insert j t, χ i x * φ x) =
          fun x => χ j x * φ x + ∑ i ∈ t, χ i x * φ x := by
        funext x
        rw [Finset.sum_insert hj]
      have hA := hadd _ _ h1 h2
      rw [e, hA, ih, Finset.sum_insert hj]
  rw [hsplit, hsum Finset.univ]
  exact Finset.sum_eq_zero fun i _ => hloc i _ (hpieces i)

end MatedCRT
